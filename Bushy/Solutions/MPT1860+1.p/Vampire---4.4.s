%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t28_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Theorem 60.55s
% Output     : Refutation 60.55s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 731 expanded)
%              Number of leaves         :   16 ( 279 expanded)
%              Depth                    :   17
%              Number of atoms          :  322 (4766 expanded)
%              Number of equality atoms :   53 ( 250 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83313,f80022])).

fof(f80022,plain,(
    k3_xboole_0(sK2,sK8(sK0,sK1,sK7(sK0,sK2))) != sK7(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f998,f997,f6776])).

fof(f6776,plain,(
    ! [X0] :
      ( k3_xboole_0(sK2,X0) != sK7(sK0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f1279,f318])).

fof(f318,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',commutativity_k3_xboole_0)).

fof(f1279,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,sK2) != sK7(sK0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1278,f237])).

fof(f237,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f182])).

fof(f182,plain,
    ( ~ v2_tex_2(sK2,sK0)
    & v2_tex_2(sK1,sK0)
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f107,f181,f180,f179])).

fof(f179,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(X2,X0)
                & v2_tex_2(X1,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(X2,sK0)
              & v2_tex_2(X1,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f180,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(X2,X0)
            & v2_tex_2(sK1,X0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(X2,X0)
          & v2_tex_2(X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(sK2,X0)
        & v2_tex_2(X1,X0)
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X1,X0)
                    & r1_tarski(X2,X1) )
                 => v2_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t28_tex_2)).

fof(f1278,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,sK2) != sK7(sK0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f1277,f239])).

fof(f239,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f182])).

fof(f1277,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,sK2) != sK7(sK0,sK2)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f1275,f242])).

fof(f242,plain,(
    ~ v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f182])).

fof(f1275,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,sK2) != sK7(sK0,sK2)
      | v2_tex_2(sK2,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f266,f461])).

fof(f461,plain,(
    ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(backward_demodulation,[],[f453,f454])).

fof(f454,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f239,f334])).

fof(f334,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',commutativity_k9_subset_1)).

fof(f453,plain,(
    ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(unit_resulting_resolution,[],[f239,f333])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f170])).

fof(f170,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',redefinition_k9_subset_1)).

fof(f266,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK7(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK7(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK7(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK8(X0,X1,X4)) = X4
                    & v3_pre_topc(sK8(X0,X1,X4),X0)
                    & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f192,f194,f193])).

fof(f193,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK7(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK8(X0,X1,X4)) = X4
        & v3_pre_topc(sK8(X0,X1,X4),X0)
        & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f192,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f191])).

fof(f191,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',d5_tex_2)).

fof(f997,plain,(
    m1_subset_1(sK8(sK0,sK1,sK7(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f237,f241,f238,f635,f448,f261])).

fof(f261,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f448,plain,(
    m1_subset_1(sK7(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f237,f242,f239,f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f635,plain,(
    r1_tarski(sK7(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f240,f449,f336])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f174])).

fof(f174,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t1_xboole_1)).

fof(f449,plain,(
    r1_tarski(sK7(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f237,f242,f239,f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK7(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f240,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f182])).

fof(f238,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f182])).

fof(f241,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f182])).

fof(f998,plain,(
    v3_pre_topc(sK8(sK0,sK1,sK7(sK0,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f237,f241,f635,f238,f448,f262])).

fof(f262,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK8(X0,X1,X4),X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f83313,plain,(
    k3_xboole_0(sK2,sK8(sK0,sK1,sK7(sK0,sK2))) = sK7(sK0,sK2) ),
    inference(forward_demodulation,[],[f83312,f6901])).

fof(f6901,plain,(
    k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))) = sK7(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f635,f448,f1489])).

fof(f1489,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_xboole_0(sK1,sK8(sK0,sK1,X5)) = X5
      | ~ r1_tarski(X5,sK1) ) ),
    inference(forward_demodulation,[],[f1488,f318])).

fof(f1488,plain,(
    ! [X5] :
      ( k3_xboole_0(sK8(sK0,sK1,X5),sK1) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,sK1) ) ),
    inference(forward_demodulation,[],[f1487,f408])).

fof(f408,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(backward_demodulation,[],[f400,f401])).

fof(f401,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f238,f334])).

fof(f400,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(unit_resulting_resolution,[],[f238,f333])).

fof(f1487,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK8(sK0,sK1,X5)) = X5 ) ),
    inference(subsumption_resolution,[],[f1459,f241])).

fof(f1459,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(sK1,sK0)
      | ~ r1_tarski(X5,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK8(sK0,sK1,X5)) = X5 ) ),
    inference(resolution,[],[f370,f238])).

fof(f370,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X3,sK0)
      | ~ r1_tarski(X2,X3)
      | k9_subset_1(u1_struct_0(sK0),X3,sK8(sK0,X3,X2)) = X2 ) ),
    inference(resolution,[],[f237,f263])).

fof(f263,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK8(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f195])).

fof(f83312,plain,(
    k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))) = k3_xboole_0(sK2,sK8(sK0,sK1,sK7(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f83311,f14638])).

fof(f14638,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f317,f2688,f336])).

fof(f2688,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k3_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(superposition,[],[f426,f318])).

fof(f426,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),k3_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f397,f330])).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t26_xboole_1)).

fof(f397,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f238,f326])).

fof(f326,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f210])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t3_subset)).

fof(f317,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t17_xboole_1)).

fof(f83311,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))),sK8(sK0,sK1,sK7(sK0,sK2)))
    | k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))) = k3_xboole_0(sK2,sK8(sK0,sK1,sK7(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f83075,f449])).

fof(f83075,plain,
    ( ~ r1_tarski(sK7(sK0,sK2),sK2)
    | ~ r1_tarski(k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))),sK8(sK0,sK1,sK7(sK0,sK2)))
    | k3_xboole_0(sK1,sK8(sK0,sK1,sK7(sK0,sK2))) = k3_xboole_0(sK2,sK8(sK0,sK1,sK7(sK0,sK2))) ),
    inference(superposition,[],[f6241,f6901])).

fof(f6241,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_xboole_0(sK1,X1),sK2)
      | ~ r1_tarski(k3_xboole_0(sK1,X1),X1)
      | k3_xboole_0(sK1,X1) = k3_xboole_0(sK2,X1) ) ),
    inference(resolution,[],[f876,f337])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f176])).

fof(f176,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',t19_xboole_1)).

fof(f876,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_xboole_0(sK1,X2),k3_xboole_0(sK2,X2))
      | k3_xboole_0(sK1,X2) = k3_xboole_0(sK2,X2) ) ),
    inference(resolution,[],[f373,f325])).

fof(f325,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t28_tex_2.p',d10_xboole_0)).

fof(f373,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f240,f330])).
%------------------------------------------------------------------------------
