%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:33 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 605 expanded)
%              Number of leaves         :   14 ( 192 expanded)
%              Depth                    :   68
%              Number of atoms          : 1250 (5853 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(subsumption_resolution,[],[f862,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
              | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
              | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
            & r1_xboole_0(u1_struct_0(X2),X1)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X2,k6_tmap_1(sK0,sK1))
            | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))
            | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2)) )
          & r1_xboole_0(u1_struct_0(X2),sK1)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X2,k6_tmap_1(sK0,sK1))
          | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,sK1)))
          | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2)) )
        & r1_xboole_0(u1_struct_0(X2),sK1)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
      & r1_xboole_0(u1_struct_0(sK2),sK1)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_tmap_1)).

fof(f862,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f858,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f858,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f857,f87])).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f86,f55])).

fof(f86,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f58])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f857,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f839,f64])).

fof(f839,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f838,f134])).

fof(f134,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f133,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f132,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f131,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f76,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f838,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f830,f64])).

fof(f830,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f829,f53])).

fof(f829,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f828,f54])).

fof(f828,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f827,f55])).

fof(f827,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f826,f56])).

fof(f826,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f821])).

fof(f821,plain,
    ( ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f808,f183])).

fof(f183,plain,(
    ! [X21,X22,X20] :
      ( v1_funct_1(k2_tmap_1(X21,k6_tmap_1(X21,X22),k7_tmap_1(X21,X22),X20))
      | ~ l1_struct_0(X20)
      | ~ l1_struct_0(k6_tmap_1(X21,X22))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f182,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f182,plain,(
    ! [X21,X22,X20] :
      ( ~ l1_struct_0(X20)
      | v1_funct_1(k2_tmap_1(X21,k6_tmap_1(X21,X22),k7_tmap_1(X21,X22),X20))
      | ~ v1_funct_2(k7_tmap_1(X21,X22),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,X22)))
      | ~ l1_struct_0(k6_tmap_1(X21,X22))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f181,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f181,plain,(
    ! [X21,X22,X20] :
      ( ~ l1_struct_0(X20)
      | v1_funct_1(k2_tmap_1(X21,k6_tmap_1(X21,X22),k7_tmap_1(X21,X22),X20))
      | ~ v1_funct_2(k7_tmap_1(X21,X22),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,X22)))
      | ~ v1_funct_1(k7_tmap_1(X21,X22))
      | ~ l1_struct_0(k6_tmap_1(X21,X22))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f179,f64])).

fof(f179,plain,(
    ! [X21,X22,X20] :
      ( ~ l1_struct_0(X20)
      | v1_funct_1(k2_tmap_1(X21,k6_tmap_1(X21,X22),k7_tmap_1(X21,X22),X20))
      | ~ v1_funct_2(k7_tmap_1(X21,X22),u1_struct_0(X21),u1_struct_0(k6_tmap_1(X21,X22)))
      | ~ v1_funct_1(k7_tmap_1(X21,X22))
      | ~ l1_struct_0(k6_tmap_1(X21,X22))
      | ~ l1_struct_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21) ) ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f808,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f807,f53])).

fof(f807,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f806,f54])).

fof(f806,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f805,f55])).

fof(f805,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f800,f56])).

fof(f800,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f791,f78])).

fof(f791,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f790,f53])).

fof(f790,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f789,f54])).

fof(f789,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f788,f55])).

fof(f788,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f783,f56])).

fof(f783,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f778,f79])).

fof(f778,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f777,f53])).

fof(f777,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f776,f54])).

fof(f776,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f775,f55])).

fof(f775,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f774,f56])).

fof(f774,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f773,f58])).

fof(f773,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f772,f59])).

fof(f59,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f772,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f771,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f771,plain,
    ( v2_struct_0(sK2)
    | ~ r1_xboole_0(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f762])).

fof(f762,plain,
    ( v2_struct_0(sK2)
    | ~ r1_xboole_0(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f761,f269])).

fof(f269,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f268,f141])).

fof(f141,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f140,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f138,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f77,f56])).

fof(f268,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f196,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f196,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f193,f141])).

fof(f193,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f85,f60])).

fof(f60,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f761,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X0,k6_tmap_1(X1,X2))
      | v2_struct_0(X0)
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(k6_tmap_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f760,f78])).

fof(f760,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X0,k6_tmap_1(X1,X2))
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
      | ~ l1_struct_0(k6_tmap_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f759,f79])).

fof(f759,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X0,k6_tmap_1(X1,X2))
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
      | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
      | ~ l1_struct_0(k6_tmap_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f758,f77])).

fof(f758,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X0,k6_tmap_1(X1,X2))
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
      | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
      | ~ v1_funct_1(k7_tmap_1(X1,X2))
      | ~ l1_struct_0(k6_tmap_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f751,f64])).

fof(f751,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X0),X0,k6_tmap_1(X1,X2))
      | ~ r1_xboole_0(u1_struct_0(X0),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
      | ~ v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
      | ~ v1_funct_1(k7_tmap_1(X1,X2))
      | ~ l1_struct_0(k6_tmap_1(X1,X2))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f721,f84])).

fof(f721,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f720,f78])).

fof(f720,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f719,f79])).

fof(f719,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f718,f65])).

fof(f718,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f717,f77])).

fof(f717,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f716,f76])).

fof(f716,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f715,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f715,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f714,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f714,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f713,f64])).

fof(f713,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f712,f64])).

fof(f712,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f711,f64])).

fof(f711,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f710,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f710,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f703])).

fof(f703,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f526,f225])).

fof(f225,plain,(
    ! [X24,X23,X21,X22] :
      ( m1_subset_1(sK3(X21,X22,k2_tmap_1(X23,X21,X24,X22)),u1_struct_0(X22))
      | v5_pre_topc(k2_tmap_1(X23,X21,X24,X22),X22,X21)
      | ~ v1_funct_2(k2_tmap_1(X23,X21,X24,X22),u1_struct_0(X22),u1_struct_0(X21))
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
      | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X21))
      | ~ v1_funct_1(X24)
      | ~ l1_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f224,f64])).

fof(f224,plain,(
    ! [X24,X23,X21,X22] :
      ( m1_subset_1(sK3(X21,X22,k2_tmap_1(X23,X21,X24,X22)),u1_struct_0(X22))
      | v5_pre_topc(k2_tmap_1(X23,X21,X24,X22),X22,X21)
      | ~ v1_funct_2(k2_tmap_1(X23,X21,X24,X22),u1_struct_0(X22),u1_struct_0(X21))
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
      | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X21))
      | ~ v1_funct_1(X24)
      | ~ l1_struct_0(X21)
      | ~ l1_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f223,f64])).

fof(f223,plain,(
    ! [X24,X23,X21,X22] :
      ( m1_subset_1(sK3(X21,X22,k2_tmap_1(X23,X21,X24,X22)),u1_struct_0(X22))
      | v5_pre_topc(k2_tmap_1(X23,X21,X24,X22),X22,X21)
      | ~ v1_funct_2(k2_tmap_1(X23,X21,X24,X22),u1_struct_0(X22),u1_struct_0(X21))
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ l1_struct_0(X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
      | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X21))
      | ~ v1_funct_1(X24)
      | ~ l1_struct_0(X21)
      | ~ l1_struct_0(X23) ) ),
    inference(subsumption_resolution,[],[f216,f83])).

fof(f216,plain,(
    ! [X24,X23,X21,X22] :
      ( m1_subset_1(sK3(X21,X22,k2_tmap_1(X23,X21,X24,X22)),u1_struct_0(X22))
      | v5_pre_topc(k2_tmap_1(X23,X21,X24,X22),X22,X21)
      | ~ v1_funct_2(k2_tmap_1(X23,X21,X24,X22),u1_struct_0(X22),u1_struct_0(X21))
      | ~ v1_funct_1(k2_tmap_1(X23,X21,X24,X22))
      | ~ l1_pre_topc(X22)
      | ~ v2_pre_topc(X22)
      | v2_struct_0(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ l1_struct_0(X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
      | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X21))
      | ~ v1_funct_1(X24)
      | ~ l1_struct_0(X21)
      | ~ l1_struct_0(X23) ) ),
    inference(resolution,[],[f69,f85])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | v5_pre_topc(X2,X1,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f526,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f525,f78])).

fof(f525,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f524,f79])).

fof(f524,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ l1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f523,f77])).

fof(f523,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f522,f64])).

fof(f522,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f515,f83])).

fof(f515,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f241,f85])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f240,f71])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f239,f65])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f238,f76])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f237,f73])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f236,f74])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(sK3(k6_tmap_1(X0,X1),X2,k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)),u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK3(X0,X1,X2))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------
