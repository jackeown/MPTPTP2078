%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t60_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 36.59s
% Output     : Refutation 36.59s
% Verified   : 
% Statistics : Number of formulae       :  173 (1302 expanded)
%              Number of leaves         :   16 ( 609 expanded)
%              Depth                    :   71
%              Number of atoms          : 1342 (17831 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10520,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10519,f417])).

fof(f417,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f361,plain,
    ( ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
      | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) )
    & r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f164,f360,f359,f358,f357,f356])).

fof(f356,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                        & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
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
                      ( ( ~ r2_hidden(k4_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                        | ~ r2_hidden(k3_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
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

fof(f357,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,sK1),X3))
                      | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,sK1),X3)) )
                    & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,sK1),X3))
                    & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,sK1),X3))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v20_lattices(sK1,X0)
        & v19_lattices(sK1,X0)
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f358,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                    | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                  & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r2_hidden(k4_lattices(X0,sK2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  | ~ r2_hidden(k3_lattices(X0,sK2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
              & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
              & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),sK3))
              | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),sK3)) )
            & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),sK3))
            & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),sK3))
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f360,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
            | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
          & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
          & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(k4_lattices(X0,X2,sK4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
          | ~ r2_hidden(k3_lattices(X0,X2,sK4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
        & r2_hidden(sK4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
        & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f164,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
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
    inference(flattening,[],[f163])).

fof(f163,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                       => ( ( r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                            & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                         => ( r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                            & r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                     => ( ( r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                       => ( r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          & r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',t60_filter_1)).

fof(f10519,plain,(
    ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10518,f414])).

fof(f414,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f10518,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10517,f415])).

fof(f415,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f10517,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f10514,f491])).

fof(f491,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f205])).

fof(f205,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',cc1_lattices)).

fof(f10514,plain,(
    ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10513,f417])).

fof(f10513,plain,
    ( ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10512,f414])).

fof(f10512,plain,
    ( ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10511,f415])).

fof(f10511,plain,
    ( ~ v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f10508,f493])).

fof(f493,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f10508,plain,
    ( ~ v6_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10507,f417])).

fof(f10507,plain,
    ( ~ v6_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f10504,f450])).

fof(f450,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',dt_l3_lattices)).

fof(f10504,plain,
    ( ~ l2_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10503,f417])).

fof(f10503,plain,
    ( ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f10493,f449])).

fof(f449,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f10493,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10492,f414])).

fof(f10492,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f10491,f422])).

fof(f422,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f361])).

fof(f10491,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f10487,f424])).

fof(f424,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f361])).

fof(f10487,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f10478,f634])).

fof(f634,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f326])).

fof(f326,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f325])).

fof(f325,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',dt_k3_lattices)).

fof(f10478,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f10477,f414])).

fof(f10477,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f10476,f422])).

fof(f10476,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f10472,f424])).

fof(f10472,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f10470,f637])).

fof(f637,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f332])).

fof(f332,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f331])).

fof(f331,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',dt_k4_lattices)).

fof(f10470,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10469,f414])).

fof(f10469,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10468,f415])).

fof(f10468,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10467,f416])).

fof(f416,plain,(
    v3_filter_0(sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f10467,plain,
    ( ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10466,f417])).

fof(f10466,plain,
    ( ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10465,f419])).

fof(f419,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f10465,plain,
    ( ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10464,f420])).

fof(f420,plain,(
    v20_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f361])).

fof(f10464,plain,
    ( ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10463,f421])).

fof(f421,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f361])).

fof(f10463,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10462,f422])).

fof(f10462,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10461,f424])).

fof(f10461,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10460,f423])).

fof(f423,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f361])).

fof(f10460,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10459,f1624])).

fof(f1624,plain,(
    r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f1623,f414])).

fof(f1623,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1622,f415])).

fof(f1622,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1621,f416])).

fof(f1621,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1620,f417])).

fof(f1620,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1619,f418])).

fof(f418,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f361])).

fof(f1619,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1618,f419])).

fof(f1618,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1617,f420])).

fof(f1617,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1616,f421])).

fof(f1616,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1615,f422])).

fof(f1615,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1611,f423])).

fof(f1611,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
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
    inference(resolution,[],[f546,f425])).

fof(f425,plain,(
    r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f361])).

fof(f546,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
      | r2_hidden(k7_filter_0(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f372])).

fof(f372,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                    & ( r2_hidden(k7_filter_0(X0,X2,X3),X1)
                      | ~ r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) )
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
    inference(nnf_transformation,[],[f267])).

fof(f267,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) )
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
    inference(flattening,[],[f266])).

fof(f266,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) )
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
    inference(ennf_transformation,[],[f109])).

fof(f109,axiom,(
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
                 => ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',l72_filter_1)).

fof(f10459,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f10375,f1634])).

fof(f1634,plain,(
    r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1) ),
    inference(subsumption_resolution,[],[f1633,f414])).

fof(f1633,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1632,f415])).

fof(f1632,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1631,f416])).

fof(f1631,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1630,f417])).

fof(f1630,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1629,f418])).

fof(f1629,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1628,f419])).

fof(f1628,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1627,f420])).

fof(f1627,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1626,f421])).

fof(f1626,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1625,f424])).

fof(f1625,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1612,f423])).

fof(f1612,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f546,f426])).

fof(f426,plain,(
    r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f361])).

fof(f10375,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(resolution,[],[f3435,f4855])).

fof(f4855,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4854,f414])).

fof(f4854,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4853,f415])).

fof(f4853,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4852,f416])).

fof(f4852,plain,
    ( ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4851,f417])).

fof(f4851,plain,
    ( ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4850,f419])).

fof(f4850,plain,
    ( ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4849,f420])).

fof(f4849,plain,
    ( ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4848,f421])).

fof(f4848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4847,f422])).

fof(f4847,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4846,f424])).

fof(f4846,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4845,f423])).

fof(f4845,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4844,f1624])).

fof(f4844,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f4793,f1634])).

fof(f4793,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1740,f1756])).

fof(f1756,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1755,f414])).

fof(f1755,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1754,f415])).

fof(f1754,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1753,f416])).

fof(f1753,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1752,f417])).

fof(f1752,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1751,f418])).

fof(f1751,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1750,f419])).

fof(f1750,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1749,f420])).

fof(f1749,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1748,f421])).

fof(f1748,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1745,f423])).

fof(f1745,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1667,f547])).

fof(f547,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f372])).

fof(f1667,plain,
    ( ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    inference(subsumption_resolution,[],[f1666,f414])).

fof(f1666,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1665,f415])).

fof(f1665,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1664,f416])).

fof(f1664,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1663,f417])).

fof(f1663,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1662,f418])).

fof(f1662,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1661,f419])).

fof(f1661,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1660,f420])).

fof(f1660,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1659,f421])).

fof(f1659,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(subsumption_resolution,[],[f1644,f423])).

fof(f1644,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(resolution,[],[f547,f427])).

fof(f427,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f361])).

fof(f1740,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1739,f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f144])).

fof(f144,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',t7_boole)).

fof(f1739,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1738,f493])).

fof(f1738,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v6_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1737,f495])).

fof(f495,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f1737,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1718,f496])).

fof(f496,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f1718,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1711])).

fof(f1711,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f549,f519])).

fof(f519,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f236])).

fof(f236,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',t18_lattices)).

fof(f549,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
      | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f269])).

fof(f269,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
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
    inference(flattening,[],[f268])).

fof(f268,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
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
    inference(ennf_transformation,[],[f141])).

fof(f141,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',t59_filter_1)).

fof(f3435,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f3434,f608])).

fof(f3434,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f3433,f491])).

fof(f3433,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ v4_lattices(X5) ) ),
    inference(subsumption_resolution,[],[f3432,f493])).

fof(f3432,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ v6_lattices(X5) ) ),
    inference(subsumption_resolution,[],[f3431,f495])).

fof(f3431,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ v8_lattices(X5)
      | ~ v6_lattices(X5) ) ),
    inference(subsumption_resolution,[],[f3424,f496])).

fof(f3424,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ v4_lattices(X5)
      | ~ v9_lattices(X5)
      | ~ v8_lattices(X5)
      | ~ v6_lattices(X5) ) ),
    inference(duplicate_literal_removal,[],[f3417])).

fof(f3417,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(k7_filter_0(X5,k3_lattices(X5,X7,X8),X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X8,X6),X9)
      | ~ r2_hidden(k7_filter_0(X5,X7,X6),X9)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v20_lattices(X9,X5)
      | ~ v19_lattices(X9,X5)
      | v1_xboole_0(X9)
      | ~ l3_lattices(X5)
      | ~ v3_filter_0(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ v4_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v9_lattices(X5)
      | ~ v8_lattices(X5)
      | ~ v6_lattices(X5) ) ),
    inference(superposition,[],[f548,f1327])).

fof(f1327,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1326,f450])).

fof(f1326,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1321])).

fof(f1321,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f635,f518])).

fof(f518,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f235])).

fof(f235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f234])).

fof(f234,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',t17_lattices)).

fof(f635,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f328])).

fof(f328,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f327])).

fof(f327,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f130])).

fof(f130,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t60_filter_1.p',redefinition_k3_lattices)).

fof(f548,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1)
      | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f269])).
%------------------------------------------------------------------------------
