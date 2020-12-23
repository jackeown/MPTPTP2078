%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t108_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 633 expanded)
%              Number of leaves         :   21 ( 184 expanded)
%              Depth                    :   21
%              Number of atoms          :  642 (4297 expanded)
%              Number of equality atoms :   41 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22701,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22700,f269])).

fof(f269,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f199,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',cc1_relset_1)).

fof(f199,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f113,f141])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',dt_u1_orders_2)).

fof(f113,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK1,sK0) )
    & v3_orders_1(k2_wellord1(u1_orders_2(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X1,sK0) )
          & v3_orders_1(k2_wellord1(u1_orders_2(sK0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(sK1,X0) )
        & v3_orders_1(k2_wellord1(u1_orders_2(X0),sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_orders_1(k2_wellord1(u1_orders_2(X0),X1))
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',t108_orders_2)).

fof(f22700,plain,(
    ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f22403,f1466])).

fof(f1466,plain,(
    r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    inference(resolution,[],[f486,f268])).

fof(f268,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X1,X1),u1_orders_2(sK0)) ) ),
    inference(subsumption_resolution,[],[f266,f113])).

fof(f266,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X1,X1),u1_orders_2(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X1,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f263,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d9_orders_2)).

fof(f263,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f262,f109])).

fof(f109,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f262,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f261,f110])).

fof(f110,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f261,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f260,f113])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f187,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',redefinition_r3_orders_2)).

fof(f187,plain,(
    ! [X4] :
      ( r3_orders_2(sK0,X4,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f186,f110])).

fof(f186,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r3_orders_2(sK0,X4,X4)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f113])).

fof(f180,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r3_orders_2(sK0,X4,X4)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f109,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r3_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',reflexivity_r3_orders_2)).

fof(f486,plain,(
    m1_subset_1(sK4(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f374,f212])).

fof(f212,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f114,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',t4_subset)).

fof(f114,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f374,plain,(
    r2_hidden(sK4(u1_orders_2(sK0),sK1),sK1) ),
    inference(resolution,[],[f232,f269])).

fof(f232,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r2_hidden(sK4(u1_orders_2(sK0),sK1),sK1) ),
    inference(resolution,[],[f229,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f91,f92])).

fof(f92,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d7_relat_2)).

fof(f229,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f228,f113])).

fof(f228,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f227,f114])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f116,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d11_orders_2)).

fof(f116,plain,
    ( ~ v6_orders_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f22403,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(backward_demodulation,[],[f22401,f234])).

fof(f234,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK5(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    inference(resolution,[],[f229,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f22401,plain,(
    sK4(u1_orders_2(sK0),sK1) = sK5(u1_orders_2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f22400,f5287])).

fof(f5287,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),X0)) ),
    inference(superposition,[],[f1116,f288])).

fof(f288,plain,(
    ! [X0] : k2_wellord1(u1_orders_2(sK0),X0) = k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f269,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d6_wellord1)).

fof(f1116,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),k3_xboole_0(u1_orders_2(sK0),X0)) ),
    inference(resolution,[],[f572,f176])).

fof(f176,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f102,f103])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d4_xboole_0)).

fof(f572,plain,(
    ~ r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    inference(resolution,[],[f235,f269])).

fof(f235,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    inference(resolution,[],[f229,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f22400,plain,
    ( sK4(u1_orders_2(sK0),sK1) = sK5(u1_orders_2(sK0),sK1)
    | r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f22375,f5240])).

fof(f5240,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK5(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),X0)) ),
    inference(superposition,[],[f1097,f288])).

fof(f1097,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK5(u1_orders_2(sK0),sK1)),k3_xboole_0(u1_orders_2(sK0),X0)) ),
    inference(resolution,[],[f570,f176])).

fof(f570,plain,(
    ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK5(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    inference(resolution,[],[f234,f269])).

fof(f22375,plain,
    ( sK4(u1_orders_2(sK0),sK1) = sK5(u1_orders_2(sK0),sK1)
    | r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),sK5(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),sK1))
    | r2_hidden(k4_tarski(sK5(u1_orders_2(sK0),sK1),sK4(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),sK1)) ),
    inference(resolution,[],[f3191,f377])).

fof(f377,plain,(
    r2_hidden(sK5(u1_orders_2(sK0),sK1),sK1) ),
    inference(resolution,[],[f233,f269])).

fof(f233,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r2_hidden(sK5(u1_orders_2(sK0),sK1),sK1) ),
    inference(resolution,[],[f229,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r7_relat_2(X0,X1)
      | r2_hidden(sK5(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f3191,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK4(u1_orders_2(sK0),sK1) = X0
      | r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),sK1),X0),k2_wellord1(u1_orders_2(sK0),sK1))
      | r2_hidden(k4_tarski(X0,sK4(u1_orders_2(sK0),sK1)),k2_wellord1(u1_orders_2(sK0),sK1)) ) ),
    inference(resolution,[],[f347,f374])).

fof(f347,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(k4_tarski(X1,X0),k2_wellord1(u1_orders_2(sK0),sK1))
      | X0 = X1
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k4_tarski(X0,X1),k2_wellord1(u1_orders_2(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f346,f300])).

fof(f300,plain,(
    ! [X16] : v1_relat_1(k2_wellord1(u1_orders_2(sK0),X16)) ),
    inference(resolution,[],[f269,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',dt_k2_wellord1)).

fof(f346,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_wellord1(u1_orders_2(sK0),sK1))
      | r2_hidden(k4_tarski(X1,X0),k2_wellord1(u1_orders_2(sK0),sK1))
      | X0 = X1
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ v1_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) ) ),
    inference(resolution,[],[f310,f129])).

fof(f129,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | X4 = X5
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & sK2(X0,X1) != sK3(X0,X1)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f87,f88])).

fof(f88,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & sK2(X0,X1) != sK3(X0,X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d6_relat_2)).

fof(f310,plain,(
    r6_relat_2(k2_wellord1(u1_orders_2(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f309,f219])).

fof(f219,plain,(
    k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1 ),
    inference(subsumption_resolution,[],[f218,f109])).

fof(f218,plain,
    ( k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f217,f110])).

fof(f217,plain,
    ( k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f111])).

fof(f111,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f216,plain,
    ( k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f112])).

fof(f112,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f215,plain,
    ( k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f113])).

fof(f208,plain,
    ( k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f114,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(u1_orders_2(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_relat_1(k2_wellord1(u1_orders_2(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_relat_1(k2_wellord1(u1_orders_2(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_relat_1(k2_wellord1(u1_orders_2(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',t107_orders_2)).

fof(f309,plain,(
    r6_relat_2(k2_wellord1(u1_orders_2(sK0),sK1),k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f307,f300])).

fof(f307,plain,
    ( ~ v1_relat_1(k2_wellord1(u1_orders_2(sK0),sK1))
    | r6_relat_2(k2_wellord1(u1_orders_2(sK0),sK1),k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1))) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( ~ v1_relat_1(k2_wellord1(u1_orders_2(sK0),sK1))
    | r6_relat_2(k2_wellord1(u1_orders_2(sK0),sK1),k3_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)))
    | ~ v1_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) ),
    inference(resolution,[],[f225,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r6_relat_2(X0,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d14_relat_2)).

fof(f225,plain,
    ( v6_relat_2(k2_wellord1(u1_orders_2(sK0),sK1))
    | ~ v1_relat_1(k2_wellord1(u1_orders_2(sK0),sK1)) ),
    inference(resolution,[],[f115,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v3_orders_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v3_orders_1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v3_orders_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v3_orders_1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v3_orders_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v3_orders_1(X0)
      <=> ( v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_orders_1(X0)
      <=> ( v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t108_orders_2.p',d5_orders_1)).

fof(f115,plain,(
    v3_orders_1(k2_wellord1(u1_orders_2(sK0),sK1)) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
