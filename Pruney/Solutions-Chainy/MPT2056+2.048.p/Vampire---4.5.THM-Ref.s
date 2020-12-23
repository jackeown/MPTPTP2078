%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 240 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  338 (1312 expanded)
%              Number of equality atoms :   47 ( 203 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f102,f49,f181,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f76_D])).

fof(f76_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f181,plain,(
    r2_hidden(k1_xboole_0,sK2) ),
    inference(resolution,[],[f164,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f164,plain,(
    ~ r1_xboole_0(sK2,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f162,f87])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

% (18708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f84,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f70,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f25,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

% (18691)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f162,plain,
    ( sK2 != k5_xboole_0(sK2,k1_xboole_0)
    | ~ r1_xboole_0(sK2,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f161,f83])).

fof(f161,plain,(
    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f160,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    & ~ v1_xboole_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (18711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f33,plain,
    ( ? [X1] :
        ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
        & ~ v1_xboole_0(X1) )
   => ( sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
      & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
      & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f160,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f159,f42])).

fof(f42,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f158,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f158,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f157,f68])).

fof(f68,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f52,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f45,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f157,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f156,f67])).

fof(f67,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f46,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f156,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f34])).

fof(f149,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f48,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(k1_xboole_0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f73,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f52,f52,f52,f52])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

% (18693)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f60])).

% (18713)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f48,plain,(
    sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f102,plain,(
    ~ sP5(sK2) ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,
    ( ~ sP5(sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,
    ( ~ sP5(sK2)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f99,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ sP5(sK2) ),
    inference(subsumption_resolution,[],[f98,f43])).

fof(f98,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ sP5(sK2) ),
    inference(subsumption_resolution,[],[f97,f69])).

fof(f69,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f44,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v1_xboole_0(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ sP5(sK2) ),
    inference(subsumption_resolution,[],[f96,f68])).

fof(f96,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v1_xboole_0(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ sP5(sK2) ),
    inference(subsumption_resolution,[],[f95,f67])).

fof(f95,plain,
    ( ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v1_xboole_0(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ sP5(sK2) ),
    inference(resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f71,f76_D])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f53,f52,f52,f52,f52])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (18692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18701)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (18714)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (18706)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (18709)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (18700)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18707)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (18688)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (18705)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (18717)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (18695)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (18710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18702)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (18699)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (18696)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (18690)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (18717)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (18690)Refutation not found, incomplete strategy% (18690)------------------------------
% 0.21/0.53  % (18690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18690)Memory used [KB]: 10746
% 0.21/0.53  % (18690)Time elapsed: 0.119 s
% 0.21/0.53  % (18690)------------------------------
% 0.21/0.53  % (18690)------------------------------
% 0.21/0.53  % (18709)Refutation not found, incomplete strategy% (18709)------------------------------
% 0.21/0.53  % (18709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18709)Memory used [KB]: 1791
% 0.21/0.53  % (18709)Time elapsed: 0.116 s
% 0.21/0.53  % (18709)------------------------------
% 0.21/0.53  % (18709)------------------------------
% 0.21/0.53  % (18694)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18712)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (18715)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f102,f49,f181,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f76_D])).
% 0.21/0.53  fof(f76_D,plain,(
% 0.21/0.53    ( ! [X1] : (( ! [X2] : (~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    r2_hidden(k1_xboole_0,sK2)),
% 0.21/0.53    inference(resolution,[],[f164,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,k1_tarski(X0)) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f63,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ~r1_xboole_0(sK2,k1_tarski(k1_xboole_0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f162,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.53  % (18708)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0 | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f70,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f62,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : ((sP0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(definition_folding,[],[f25,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f51,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  % (18691)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    sK2 != k5_xboole_0(sK2,k1_xboole_0) | ~r1_xboole_0(sK2,k1_tarski(k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f161,f83])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    (sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (18711)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X1] : (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) => (sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,negated_conjecture,(
% 1.40/0.54    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.40/0.54    inference(negated_conjecture,[],[f14])).
% 1.40/0.54  fof(f14,conjecture,(
% 1.40/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 1.40/0.54  fof(f160,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f159,f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    l1_struct_0(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f159,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f158,f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ~v1_xboole_0(sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f158,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | v1_xboole_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f157,f68])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.40/0.54    inference(definition_unfolding,[],[f45,f52])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,axiom,(
% 1.40/0.54    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f157,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | ~v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | v1_xboole_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f156,f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.40/0.54    inference(definition_unfolding,[],[f46,f52])).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f156,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | ~v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | ~v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | v1_xboole_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f149,f66])).
% 1.40/0.54  fof(f66,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 1.40/0.54    inference(definition_unfolding,[],[f47,f52])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f149,plain,(
% 1.40/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) | ~v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | ~v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | v1_xboole_0(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(superposition,[],[f48,f105])).
% 1.40/0.54  fof(f105,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f104])).
% 1.40/0.54  fof(f104,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(k1_xboole_0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(superposition,[],[f73,f72])).
% 1.40/0.54  fof(f72,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f55,f52,f52,f52,f52])).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f23])).
% 1.40/0.54  % (18693)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,axiom,(
% 1.40/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 1.40/0.54  fof(f73,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f65,f60])).
% 1.40/0.54  % (18713)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.54  fof(f65,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    sK2 != k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    v1_xboole_0(k1_xboole_0)),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    v1_xboole_0(k1_xboole_0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    ~sP5(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f101,f41])).
% 1.40/0.54  fof(f101,plain,(
% 1.40/0.54    ~sP5(sK2) | v2_struct_0(sK1)),
% 1.40/0.54    inference(subsumption_resolution,[],[f100,f42])).
% 1.40/0.54  fof(f100,plain,(
% 1.40/0.54    ~sP5(sK2) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.40/0.54    inference(resolution,[],[f99,f54])).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.40/0.54  fof(f99,plain,(
% 1.40/0.54    v1_xboole_0(k2_struct_0(sK1)) | ~sP5(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f98,f43])).
% 1.40/0.54  fof(f98,plain,(
% 1.40/0.54    v1_xboole_0(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~sP5(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f97,f69])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 1.40/0.54    inference(definition_unfolding,[],[f44,f52])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f97,plain,(
% 1.40/0.54    ~v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) | v1_xboole_0(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~sP5(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f96,f68])).
% 1.40/0.54  fof(f96,plain,(
% 1.40/0.54    ~v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | ~v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) | v1_xboole_0(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~sP5(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f95,f67])).
% 1.40/0.54  fof(f95,plain,(
% 1.40/0.54    ~v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | ~v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) | ~v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) | v1_xboole_0(sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~sP5(sK2)),
% 1.40/0.54    inference(resolution,[],[f77,f66])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~sP5(X1)) )),
% 1.40/0.54    inference(general_splitting,[],[f71,f76_D])).
% 1.40/0.54  fof(f71,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f53,f52,f52,f52,f52])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.40/0.54    inference(flattening,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,axiom,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (18717)------------------------------
% 1.40/0.54  % (18717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (18717)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (18717)Memory used [KB]: 1791
% 1.40/0.54  % (18717)Time elapsed: 0.119 s
% 1.40/0.54  % (18717)------------------------------
% 1.40/0.54  % (18717)------------------------------
% 1.40/0.54  % (18693)Refutation not found, incomplete strategy% (18693)------------------------------
% 1.40/0.54  % (18693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (18693)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (18693)Memory used [KB]: 6268
% 1.40/0.54  % (18693)Time elapsed: 0.128 s
% 1.40/0.54  % (18693)------------------------------
% 1.40/0.54  % (18693)------------------------------
% 1.40/0.54  % (18710)Refutation not found, incomplete strategy% (18710)------------------------------
% 1.40/0.54  % (18710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (18710)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (18710)Memory used [KB]: 10746
% 1.40/0.54  % (18710)Time elapsed: 0.083 s
% 1.40/0.54  % (18710)------------------------------
% 1.40/0.54  % (18710)------------------------------
% 1.40/0.54  % (18689)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.54  % (18687)Success in time 0.178 s
%------------------------------------------------------------------------------
