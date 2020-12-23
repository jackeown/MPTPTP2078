%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1464+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:57 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  447 (5386 expanded)
%              Number of leaves         :   21 (2723 expanded)
%              Depth                    :  320
%              Number of atoms          : 3248 (77910 expanded)
%              Number of equality atoms :    7 (  70 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(subsumption_resolution,[],[f991,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
      | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) )
    & r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
    & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v20_lattices(sK1,sK0)
    & v19_lattices(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l3_lattices(sK0)
    & v3_filter_0(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f48,f47,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                              | ~ r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                            & r2_hidden(k7_filter_0(X0,X4,X5),X1)
                            & r2_hidden(k7_filter_0(X0,X2,X3),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,X2,X4),k4_lattices(sK0,X3,X5)),X1)
                            | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,X2,X4),k3_lattices(sK0,X3,X5)),X1) )
                          & r2_hidden(k7_filter_0(sK0,X4,X5),X1)
                          & r2_hidden(k7_filter_0(sK0,X2,X3),X1)
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v20_lattices(X1,sK0)
          & v19_lattices(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(sK0)
      & v3_filter_0(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,X2,X4),k4_lattices(sK0,X3,X5)),X1)
                          | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,X2,X4),k3_lattices(sK0,X3,X5)),X1) )
                        & r2_hidden(k7_filter_0(sK0,X4,X5),X1)
                        & r2_hidden(k7_filter_0(sK0,X2,X3),X1)
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v20_lattices(X1,sK0)
        & v19_lattices(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,X2,X4),k4_lattices(sK0,X3,X5)),sK1)
                        | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,X2,X4),k3_lattices(sK0,X3,X5)),sK1) )
                      & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
                      & r2_hidden(k7_filter_0(sK0,X2,X3),sK1)
                      & m1_subset_1(X5,u1_struct_0(sK0)) )
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v20_lattices(sK1,sK0)
      & v19_lattices(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,X2,X4),k4_lattices(sK0,X3,X5)),sK1)
                      | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,X2,X4),k3_lattices(sK0,X3,X5)),sK1) )
                    & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
                    & r2_hidden(k7_filter_0(sK0,X2,X3),sK1)
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,X4),k4_lattices(sK0,X3,X5)),sK1)
                    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,X4),k3_lattices(sK0,X3,X5)),sK1) )
                  & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
                  & r2_hidden(k7_filter_0(sK0,sK2,X3),sK1)
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,X4),k4_lattices(sK0,X3,X5)),sK1)
                  | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,X4),k3_lattices(sK0,X3,X5)),sK1) )
                & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
                & r2_hidden(k7_filter_0(sK0,sK2,X3),sK1)
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,X4),k4_lattices(sK0,sK3,X5)),sK1)
                | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,X4),k3_lattices(sK0,sK3,X5)),sK1) )
              & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
              & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
              & m1_subset_1(X5,u1_struct_0(sK0)) )
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,X4),k4_lattices(sK0,sK3,X5)),sK1)
              | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,X4),k3_lattices(sK0,sK3,X5)),sK1) )
            & r2_hidden(k7_filter_0(sK0,X4,X5),sK1)
            & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
            & m1_subset_1(X5,u1_struct_0(sK0)) )
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ? [X5] :
          ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,X5)),sK1)
            | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,X5)),sK1) )
          & r2_hidden(k7_filter_0(sK0,sK4,X5),sK1)
          & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
          & m1_subset_1(X5,u1_struct_0(sK0)) )
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X5] :
        ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,X5)),sK1)
          | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,X5)),sK1) )
        & r2_hidden(k7_filter_0(sK0,sK4,X5),sK1)
        & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
        | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) )
      & r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
      & r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
      & m1_subset_1(sK5,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            | ~ r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          & r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          & r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            | ~ r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          & r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          & r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v3_filter_0(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r2_hidden(k7_filter_0(X0,X4,X5),X1)
                                & r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                             => ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                                & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X0))
                         => ( ( r2_hidden(k7_filter_0(X0,X4,X5),X1)
                              & r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                           => ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                              & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_filter_1)).

fof(f991,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f990,f57])).

fof(f57,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f990,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f989,f59])).

fof(f59,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f989,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f988,f64])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f988,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f986,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f986,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f985,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(f985,plain,(
    ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f984,f56])).

fof(f984,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f983,f57])).

fof(f983,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f982,f59])).

fof(f982,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f981,f65])).

fof(f981,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f979,f64])).

fof(f979,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f978,f109])).

fof(f978,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f977,f65])).

fof(f977,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f976,f64])).

fof(f976,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f973,f68])).

fof(f68,plain,(
    r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f973,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f963,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(k4_filter_0(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_filter_0(sK0,X1,X0),u1_struct_0(sK0))
      | ~ r2_hidden(k7_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f125,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k7_filter_0(sK0,X1,X0) = k4_lattices(sK0,k4_filter_0(sK0,X1,X0),k4_filter_0(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_filter_0(sK0,X1,X0) = k4_lattices(sK0,k4_filter_0(sK0,X1,X0),k4_filter_0(sK0,X0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f59])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k7_filter_0(sK0,X1,X0) = k4_lattices(sK0,k4_filter_0(sK0,X1,X0),k4_filter_0(sK0,X0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f82,f57])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_filter_0)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f61,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f123,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f122,f62])).

fof(f62,plain,(
    v20_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v20_lattices(X2,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ v19_lattices(X2,sK0)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f121,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f59])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l3_lattices(sK0)
      | r2_hidden(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f112,f57])).

fof(f112,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v10_lattices(X0)
      | ~ r2_hidden(k4_lattices(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(X4,X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(k4_lattices(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X1,X0)
                & v19_lattices(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ( ( ~ r2_hidden(k4_lattices(X0,sK6(X0,X1),sK7(X0,X1)),X1)
                  | ~ r2_hidden(sK7(X0,X1),X1)
                  | ~ r2_hidden(sK6(X0,X1),X1) )
                & ( r2_hidden(k4_lattices(X0,sK6(X0,X1),sK7(X0,X1)),X1)
                  | ( r2_hidden(sK7(X0,X1),X1)
                    & r2_hidden(sK6(X0,X1),X1) ) )
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( ( r2_hidden(X5,X1)
                            & r2_hidden(X4,X1) )
                          | ~ r2_hidden(k4_lattices(X0,X4,X5),X1) )
                        & ( r2_hidden(k4_lattices(X0,X4,X5),X1)
                          | ~ r2_hidden(X5,X1)
                          | ~ r2_hidden(X4,X1) ) )
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v20_lattices(X1,X0)
              | ~ v19_lattices(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
              & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                | ( r2_hidden(X3,X1)
                  & r2_hidden(X2,X1) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ~ r2_hidden(k4_lattices(X0,sK6(X0,X1),X3),X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(sK6(X0,X1),X1) )
            & ( r2_hidden(k4_lattices(X0,sK6(X0,X1),X3),X1)
              | ( r2_hidden(X3,X1)
                & r2_hidden(sK6(X0,X1),X1) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_lattices(X0,sK6(X0,X1),X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_lattices(X0,sK6(X0,X1),X3),X1)
            | ( r2_hidden(X3,X1)
              & r2_hidden(sK6(X0,X1),X1) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(k4_lattices(X0,sK6(X0,X1),sK7(X0,X1)),X1)
          | ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r2_hidden(k4_lattices(X0,sK6(X0,X1),sK7(X0,X1)),X1)
          | ( r2_hidden(sK7(X0,X1),X1)
            & r2_hidden(sK6(X0,X1),X1) ) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X1,X0)
                & v19_lattices(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ? [X3] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ~ r2_hidden(X3,X1)
                        | ~ r2_hidden(X2,X1) )
                      & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) ) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( ( ( ( r2_hidden(X5,X1)
                            & r2_hidden(X4,X1) )
                          | ~ r2_hidden(k4_lattices(X0,X4,X5),X1) )
                        & ( r2_hidden(k4_lattices(X0,X4,X5),X1)
                          | ~ r2_hidden(X5,X1)
                          | ~ r2_hidden(X4,X1) ) )
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v20_lattices(X1,X0)
              | ~ v19_lattices(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X1,X0)
                & v19_lattices(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ? [X3] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ~ r2_hidden(X3,X1)
                        | ~ r2_hidden(X2,X1) )
                      & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) ) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ( ( ( r2_hidden(X3,X1)
                            & r2_hidden(X2,X1) )
                          | ~ r2_hidden(k4_lattices(X0,X2,X3),X1) )
                        & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                          | ~ r2_hidden(X3,X1)
                          | ~ r2_hidden(X2,X1) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v20_lattices(X1,X0)
              | ~ v19_lattices(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X1,X0)
                & v19_lattices(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ? [X3] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ~ r2_hidden(X3,X1)
                        | ~ r2_hidden(X2,X1) )
                      & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                        | ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) ) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ( ( ( r2_hidden(X3,X1)
                            & r2_hidden(X2,X1) )
                          | ~ r2_hidden(k4_lattices(X0,X2,X3),X1) )
                        & ( r2_hidden(k4_lattices(X0,X2,X3),X1)
                          | ~ r2_hidden(X3,X1)
                          | ~ r2_hidden(X2,X1) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v20_lattices(X1,X0)
              | ~ v19_lattices(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_0)).

fof(f963,plain,(
    ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f962,f66])).

fof(f66,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f962,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f961,f64])).

fof(f961,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f955,f65])).

fof(f955,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(resolution,[],[f953,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X2,X0),X1),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f158,f61])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X2,X0),X1),sK1) ) ),
    inference(subsumption_resolution,[],[f157,f63])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X2,X0),X1),sK1) ) ),
    inference(resolution,[],[f156,f62])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v20_lattices(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ v19_lattices(X2,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X3),X1),X2) ) ),
    inference(subsumption_resolution,[],[f155,f106])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X3),X1),X2) ) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X3),X1),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X3),X1),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f59])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l3_lattices(sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X3),X1),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    v3_filter_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v3_filter_0(X0)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_filter_0(X0,k4_lattices(X0,X2,X4),X3),X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(k4_filter_0(X0,k4_lattices(X0,X4,X2),X3),X1)
                        & r2_hidden(k4_filter_0(X0,k4_lattices(X0,X2,X4),X3),X1)
                        & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X4,X3)),X1)
                        & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X3,X4)),X1) )
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(k4_filter_0(X0,k4_lattices(X0,X4,X2),X3),X1)
                        & r2_hidden(k4_filter_0(X0,k4_lattices(X0,X2,X4),X3),X1)
                        & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X4,X3)),X1)
                        & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X3,X4)),X1) )
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_hidden(k4_filter_0(X0,X2,X3),X1)
                       => ( r2_hidden(k4_filter_0(X0,k4_lattices(X0,X4,X2),X3),X1)
                          & r2_hidden(k4_filter_0(X0,k4_lattices(X0,X2,X4),X3),X1)
                          & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X4,X3)),X1)
                          & r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X3,X4)),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l66_filter_1)).

fof(f953,plain,(
    ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f952,f56])).

fof(f952,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f951,f57])).

fof(f951,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f950,f59])).

fof(f950,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f949,f66])).

fof(f949,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f947,f67])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f947,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f946,f109])).

fof(f946,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f945,f56])).

fof(f945,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f944,f57])).

fof(f944,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f943,f59])).

fof(f943,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f942,f67])).

fof(f942,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f940,f66])).

fof(f940,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f933,f109])).

fof(f933,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f932,f67])).

fof(f932,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f931,f66])).

fof(f931,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f928,f69])).

fof(f69,plain,(
    r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f928,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(resolution,[],[f921,f126])).

fof(f921,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f920,f64])).

fof(f920,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f919,f66])).

fof(f919,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f915,f67])).

fof(f915,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f914,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X2),X1),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X2),X1),sK1) ) ),
    inference(subsumption_resolution,[],[f166,f63])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X2,X1),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X0,X2),X1),sK1) ) ),
    inference(resolution,[],[f165,f62])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v20_lattices(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ v19_lattices(X2,sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X3,X0),X1),X2) ) ),
    inference(subsumption_resolution,[],[f164,f106])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X3,X0),X1),X2) ) ),
    inference(subsumption_resolution,[],[f163,f56])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X3,X0),X1),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f57])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X3,X0),X1),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f59])).

fof(f161,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l3_lattices(sK0)
      | r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,X3,X0),X1),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v3_filter_0(X0)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_filter_0(X0,k4_lattices(X0,X4,X2),X3),X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f914,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f913,f59])).

fof(f913,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f912,f56])).

fof(f912,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f911,f57])).

fof(f911,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f910,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f910,plain,
    ( ~ v6_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f909,f59])).

fof(f909,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f908,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f908,plain,
    ( ~ l1_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f907,f56])).

fof(f907,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f906,f64])).

fof(f906,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f904,f66])).

fof(f904,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f844,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f844,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f843,f65])).

fof(f843,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f836,f67])).

fof(f836,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(resolution,[],[f833,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X1,X2)),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X2),sK1)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f177,f61])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X2),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X1,X2)),sK1) ) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X2),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X1,X2)),sK1) ) ),
    inference(resolution,[],[f175,f62])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v20_lattices(X2,sK0)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X3),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ v19_lattices(X2,sK0)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X3,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f174,f106])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X3),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X3,X1)),X2) ) ),
    inference(subsumption_resolution,[],[f173,f56])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X3),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X3,X1)),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f57])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X3),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X3,X1)),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_filter_0(sK0,X0,X1),X2)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X3),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l3_lattices(sK0)
      | r2_hidden(k4_filter_0(sK0,X0,k4_lattices(sK0,X3,X1)),X2)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v3_filter_0(X0)
      | ~ r2_hidden(k4_filter_0(X0,X2,X4),X1)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_filter_0(X0,X2,k4_lattices(X0,X3,X4)),X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k4_filter_0(X0,X2,k4_lattices(X0,X3,X4)),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X4),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k4_filter_0(X0,X2,k4_lattices(X0,X3,X4)),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X4),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( ( r2_hidden(k4_filter_0(X0,X2,X4),X1)
                          & r2_hidden(k4_filter_0(X0,X2,X3),X1) )
                       => r2_hidden(k4_filter_0(X0,X2,k4_lattices(X0,X3,X4)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l70_filter_1)).

fof(f833,plain,(
    ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f832,f56])).

fof(f832,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f831,f57])).

fof(f831,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f830,f59])).

fof(f830,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f829,f64])).

fof(f829,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f827,f65])).

fof(f827,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f826,f109])).

fof(f826,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f825,f56])).

fof(f825,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f824,f57])).

fof(f824,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f823,f59])).

fof(f823,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f822,f65])).

fof(f822,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f820,f64])).

fof(f820,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f819,f109])).

fof(f819,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f818,f65])).

fof(f818,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f817,f64])).

fof(f817,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f815,f68])).

fof(f815,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f806,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_filter_0(sK0,X1,X0),sK1)
      | ~ m1_subset_1(k4_filter_0(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_filter_0(sK0,X1,X0),u1_struct_0(sK0))
      | ~ r2_hidden(k7_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f133,f116])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f132,f61])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f131,f63])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,X1,X0),sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f130,f62])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v20_lattices(X2,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ v19_lattices(X2,sK0)
      | r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f129,f106])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f128,f56])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | r2_hidden(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f59])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X2,sK0)
      | ~ v19_lattices(X2,sK0)
      | v1_xboole_0(X2)
      | ~ l3_lattices(sK0)
      | r2_hidden(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f113,f57])).

fof(f113,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v10_lattices(X0)
      | ~ r2_hidden(k4_lattices(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(X5,X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_lattices(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f806,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f805,f67])).

fof(f805,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f804,f65])).

fof(f804,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f798,f64])).

fof(f798,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(resolution,[],[f796,f159])).

fof(f796,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f795,f56])).

fof(f795,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f794,f57])).

fof(f794,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f793,f59])).

fof(f793,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f792,f66])).

fof(f792,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f790,f67])).

fof(f790,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f789,f109])).

fof(f789,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(subsumption_resolution,[],[f788,f56])).

fof(f788,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f787,f57])).

fof(f787,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f786,f59])).

fof(f786,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f785,f67])).

fof(f785,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f783,f66])).

fof(f783,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f776,f109])).

fof(f776,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(subsumption_resolution,[],[f775,f67])).

fof(f775,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f774,f66])).

fof(f774,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f772,f69])).

fof(f772,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(resolution,[],[f766,f134])).

fof(f766,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f765,f65])).

fof(f765,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f764,f67])).

fof(f764,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f760,f66])).

fof(f760,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f759,f168])).

fof(f759,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(subsumption_resolution,[],[f758,f59])).

fof(f758,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f757,f56])).

fof(f757,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f756,f57])).

fof(f756,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f755,f75])).

fof(f755,plain,
    ( ~ v6_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1) ),
    inference(subsumption_resolution,[],[f754,f59])).

fof(f754,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f753,f71])).

fof(f753,plain,
    ( ~ l1_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f752,f56])).

fof(f752,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f751,f65])).

fof(f751,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f749,f67])).

fof(f749,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f689,f108])).

fof(f689,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(subsumption_resolution,[],[f688,f64])).

fof(f688,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(subsumption_resolution,[],[f681,f66])).

fof(f681,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),sK2),sK1) ),
    inference(resolution,[],[f678,f178])).

fof(f678,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f677,f56])).

fof(f677,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f676,f57])).

fof(f676,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f675,f59])).

fof(f675,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f674,f64])).

fof(f674,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f672,f65])).

fof(f672,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f671,f109])).

fof(f671,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f670,f56])).

fof(f670,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f669,f57])).

fof(f669,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f668,f59])).

fof(f668,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f667,f65])).

fof(f667,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f665,f64])).

fof(f665,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f664,f109])).

fof(f664,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f663,f65])).

fof(f663,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f662,f64])).

fof(f662,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f659,f68])).

fof(f659,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f651,f126])).

fof(f651,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f650,f56])).

fof(f650,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f649,f57])).

fof(f649,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f648,f58])).

fof(f648,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f647,f59])).

fof(f647,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f646,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f646,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f645,f61])).

fof(f645,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f644,f62])).

fof(f644,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f643,f63])).

fof(f643,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f642,f64])).

fof(f642,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f641,f65])).

fof(f641,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f627,f67])).

fof(f627,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f623,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X3,X4)),X1)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f623,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f622,f56])).

fof(f622,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f621,f57])).

fof(f621,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f620,f59])).

fof(f620,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f619,f66])).

fof(f619,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f617,f67])).

fof(f617,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f616,f109])).

fof(f616,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f615,f56])).

fof(f615,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f614,f57])).

fof(f614,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f613,f59])).

fof(f613,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f612,f67])).

fof(f612,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f610,f66])).

fof(f610,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f603,f109])).

fof(f603,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f602,f67])).

fof(f602,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f601,f66])).

fof(f601,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f598,f69])).

fof(f598,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(resolution,[],[f585,f126])).

fof(f585,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f584,f56])).

fof(f584,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f583,f57])).

fof(f583,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f582,f58])).

fof(f582,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f581,f59])).

fof(f581,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f580,f60])).

fof(f580,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f579,f61])).

fof(f579,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f578,f62])).

fof(f578,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f577,f63])).

fof(f577,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f66])).

fof(f576,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f575,f67])).

fof(f575,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f571,f65])).

fof(f571,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f568,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_filter_0(X0,X2,k3_lattices(X0,X4,X3)),X1)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f568,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f567,f59])).

fof(f567,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f566,f56])).

fof(f566,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f565,f57])).

fof(f565,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f564,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f564,plain,
    ( ~ v4_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f563,f59])).

fof(f563,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f562,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f562,plain,
    ( ~ l2_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f561,f56])).

fof(f561,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f560,f65])).

fof(f560,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f558,f67])).

fof(f558,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f464,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f464,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f463,f56])).

fof(f463,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f462,f57])).

fof(f462,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f461,f58])).

fof(f461,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f460,f59])).

fof(f460,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f459,f60])).

fof(f459,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f458,f61])).

fof(f458,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f457,f62])).

fof(f457,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f456,f63])).

fof(f456,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f455,f64])).

fof(f455,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f452,f66])).

fof(f452,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK4,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK2,k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f449,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_filter_0(X0,k3_lattices(X0,X2,X4),X3),X1)
      | ~ r2_hidden(k4_filter_0(X0,X4,X3),X1)
      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k4_filter_0(X0,k3_lattices(X0,X2,X4),X3),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X4,X3),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k4_filter_0(X0,k3_lattices(X0,X2,X4),X3),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X4,X3),X1)
                      | ~ r2_hidden(k4_filter_0(X0,X2,X3),X1)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( ( r2_hidden(k4_filter_0(X0,X4,X3),X1)
                          & r2_hidden(k4_filter_0(X0,X2,X3),X1) )
                       => r2_hidden(k4_filter_0(X0,k3_lattices(X0,X2,X4),X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_filter_1)).

fof(f449,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f448,f56])).

fof(f448,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f447,f57])).

fof(f447,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f59])).

fof(f446,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f445,f64])).

fof(f445,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f443,f65])).

fof(f443,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f442,f109])).

fof(f442,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f441,f56])).

fof(f441,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f440,f57])).

fof(f440,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f439,f59])).

fof(f439,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f438,f65])).

fof(f438,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f436,f64])).

fof(f436,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f435,f109])).

fof(f435,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f434,f65])).

fof(f434,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f433,f64])).

fof(f433,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f431,f68])).

fof(f431,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f424,f134])).

fof(f424,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f423,f56])).

fof(f423,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f422,f57])).

fof(f422,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f421,f58])).

fof(f421,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f420,f59])).

fof(f420,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f419,f60])).

fof(f419,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f418,f61])).

fof(f418,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f417,f62])).

fof(f417,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f416,f63])).

fof(f416,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f415,f65])).

fof(f415,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f414,f64])).

fof(f414,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f400,f66])).

fof(f400,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,sK2),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f396,f76])).

fof(f396,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f395,f56])).

fof(f395,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f394,f57])).

fof(f394,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f393,f59])).

fof(f393,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f392,f66])).

fof(f392,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f390,f67])).

fof(f390,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f389,f109])).

fof(f389,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f388,f56])).

fof(f388,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f387,f57])).

fof(f387,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f386,f59])).

fof(f386,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f385,f67])).

fof(f385,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f383,f66])).

fof(f383,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f376,f109])).

fof(f376,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f375,f67])).

fof(f375,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f374,f66])).

fof(f374,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f372,f69])).

fof(f372,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK4,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK5,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,sK4,sK5),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(resolution,[],[f360,f134])).

fof(f360,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f359,f56])).

fof(f359,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f358,f57])).

fof(f358,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f357,f58])).

fof(f357,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f356,f59])).

fof(f356,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f355,f60])).

fof(f355,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f354,f61])).

fof(f354,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f353,f62])).

fof(f353,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f352,f63])).

fof(f352,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f351,f67])).

fof(f351,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f350,f66])).

fof(f350,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f346,f64])).

fof(f346,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,sK4),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f343,f77])).

fof(f343,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f342,f59])).

fof(f342,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f341,f56])).

fof(f341,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f340,f57])).

fof(f340,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f339,f74])).

fof(f339,plain,
    ( ~ v4_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f338,f59])).

fof(f338,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f337,f72])).

fof(f337,plain,
    ( ~ l2_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f336,f56])).

fof(f336,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f335,f64])).

fof(f335,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f333,f66])).

fof(f333,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f240,f107])).

fof(f240,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f239,f56])).

fof(f239,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f238,f57])).

fof(f238,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f237,f58])).

fof(f237,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f59])).

fof(f236,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f60])).

fof(f235,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f234,f61])).

fof(f234,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f62])).

fof(f233,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f63])).

fof(f232,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f65])).

fof(f231,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f67])).

fof(f226,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK5,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,sK3,k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f223,f81])).

fof(f223,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f222,f59])).

fof(f222,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f221,f56])).

fof(f221,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f220,f57])).

fof(f220,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f219,f75])).

fof(f219,plain,
    ( ~ v6_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f218,f59])).

fof(f218,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f217,f71])).

fof(f217,plain,
    ( ~ l1_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f216,f56])).

fof(f216,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f64])).

fof(f215,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f66])).

fof(f213,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f212,f108])).

fof(f212,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f211,f59])).

fof(f211,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f210,f56])).

fof(f210,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f209,f57])).

fof(f209,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f208,f75])).

fof(f208,plain,
    ( ~ v6_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f207,f59])).

fof(f207,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f206,f71])).

fof(f206,plain,
    ( ~ l1_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f205,f56])).

fof(f205,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f65])).

fof(f204,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f201,f108])).

fof(f201,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f200,f59])).

fof(f200,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f199,f56])).

fof(f199,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f198,f57])).

fof(f198,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f197,f74])).

fof(f197,plain,
    ( ~ v4_lattices(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f196,f59])).

fof(f196,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f195,f72])).

fof(f195,plain,
    ( ~ l2_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f194,f56])).

fof(f194,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f193,f64])).

fof(f193,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f66])).

fof(f191,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f190,f107])).

fof(f190,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f189,f59])).

fof(f189,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f188,f56])).

fof(f188,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f187,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f186,f74])).

fof(f186,plain,
    ( ~ v4_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1) ),
    inference(subsumption_resolution,[],[f185,f59])).

fof(f185,plain,
    ( ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f184,f72])).

fof(f184,plain,
    ( ~ l2_lattices(sK0)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f183,f56])).

fof(f183,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f65])).

fof(f182,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f180,f67])).

fof(f180,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f170,f107])).

fof(f170,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK3,sK5),k4_lattices(sK0,sK2,sK4)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK5),u1_struct_0(sK0)) ),
    inference(resolution,[],[f151,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_filter_0(sK0,X0,X1),sK1)
      | ~ r2_hidden(k4_filter_0(sK0,X1,X0),sK1)
      | ~ r2_hidden(k4_filter_0(sK0,X0,X1),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f143,f116])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_lattices(sK0,X0,X1),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_lattices(sK0,X0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f141,f63])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ v19_lattices(sK1,sK0)
      | r2_hidden(k4_lattices(sK0,X0,X1),sK1) ) ),
    inference(resolution,[],[f140,f62])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v20_lattices(X1,sK0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v19_lattices(X1,sK0)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f139,f106])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X1,sK0)
      | ~ v19_lattices(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f138,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X1,sK0)
      | ~ v19_lattices(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f137,f110])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X1,sK0)
      | ~ v19_lattices(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f136,f56])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X1,sK0)
      | ~ v19_lattices(X1,sK0)
      | v1_xboole_0(X1)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f135,f59])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v20_lattices(X1,sK0)
      | ~ v19_lattices(X1,sK0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(sK0)
      | r2_hidden(k4_lattices(sK0,X2,X0),X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v10_lattices(X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_lattices(X0,X4,X5),X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_lattices(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f151,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK5),u1_struct_0(sK0))
    | ~ r2_hidden(k4_filter_0(sK0,k3_lattices(sK0,sK3,sK5),k3_lattices(sK0,sK2,sK4)),sK1) ),
    inference(resolution,[],[f148,f70])).

fof(f70,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),k3_lattices(sK0,sK3,sK5)),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),k4_lattices(sK0,sK3,sK5)),sK1) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
