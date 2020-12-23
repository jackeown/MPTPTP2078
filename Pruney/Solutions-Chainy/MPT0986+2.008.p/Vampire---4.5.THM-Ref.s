%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:26 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   44 (  94 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 563 expanded)
%              Number of equality atoms :   62 ( 174 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f23])).

fof(f23,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v2_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f59,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f51,f58])).

fof(f58,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f55,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f55,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f20,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f31,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f51,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f50,f43])).

fof(f43,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f42,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f50,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f19,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f22,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f25,plain,(
    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1225392128)
% 0.13/0.36  ipcrm: permission denied for id (1226506241)
% 0.13/0.36  ipcrm: permission denied for id (1226571779)
% 0.13/0.37  ipcrm: permission denied for id (1226604548)
% 0.13/0.37  ipcrm: permission denied for id (1226637317)
% 0.13/0.37  ipcrm: permission denied for id (1226670086)
% 0.13/0.37  ipcrm: permission denied for id (1230143495)
% 0.13/0.37  ipcrm: permission denied for id (1226735624)
% 0.13/0.37  ipcrm: permission denied for id (1225424905)
% 0.13/0.37  ipcrm: permission denied for id (1226768394)
% 0.13/0.37  ipcrm: permission denied for id (1225490443)
% 0.13/0.38  ipcrm: permission denied for id (1230176268)
% 0.13/0.38  ipcrm: permission denied for id (1226833933)
% 0.13/0.38  ipcrm: permission denied for id (1230209038)
% 0.13/0.38  ipcrm: permission denied for id (1226899471)
% 0.13/0.38  ipcrm: permission denied for id (1226932240)
% 0.13/0.38  ipcrm: permission denied for id (1230241809)
% 0.13/0.38  ipcrm: permission denied for id (1226997778)
% 0.13/0.38  ipcrm: permission denied for id (1227030547)
% 0.13/0.39  ipcrm: permission denied for id (1230274580)
% 0.13/0.39  ipcrm: permission denied for id (1227096085)
% 0.13/0.39  ipcrm: permission denied for id (1230307350)
% 0.13/0.39  ipcrm: permission denied for id (1230340119)
% 0.13/0.39  ipcrm: permission denied for id (1227292699)
% 0.13/0.40  ipcrm: permission denied for id (1225588764)
% 0.13/0.40  ipcrm: permission denied for id (1230471197)
% 0.13/0.40  ipcrm: permission denied for id (1227358238)
% 0.13/0.40  ipcrm: permission denied for id (1227391007)
% 0.13/0.40  ipcrm: permission denied for id (1230503968)
% 0.13/0.40  ipcrm: permission denied for id (1227489314)
% 0.13/0.41  ipcrm: permission denied for id (1230602276)
% 0.13/0.41  ipcrm: permission denied for id (1225654309)
% 0.21/0.41  ipcrm: permission denied for id (1227587622)
% 0.21/0.41  ipcrm: permission denied for id (1230667816)
% 0.21/0.41  ipcrm: permission denied for id (1230700585)
% 0.21/0.41  ipcrm: permission denied for id (1227751467)
% 0.21/0.42  ipcrm: permission denied for id (1227849774)
% 0.21/0.42  ipcrm: permission denied for id (1230897201)
% 0.21/0.42  ipcrm: permission denied for id (1225687090)
% 0.21/0.42  ipcrm: permission denied for id (1225719859)
% 0.21/0.43  ipcrm: permission denied for id (1230929972)
% 0.21/0.43  ipcrm: permission denied for id (1230962741)
% 0.21/0.43  ipcrm: permission denied for id (1228046390)
% 0.21/0.43  ipcrm: permission denied for id (1230995511)
% 0.21/0.43  ipcrm: permission denied for id (1228111928)
% 0.21/0.43  ipcrm: permission denied for id (1231028281)
% 0.21/0.43  ipcrm: permission denied for id (1225752634)
% 0.21/0.43  ipcrm: permission denied for id (1225785403)
% 0.21/0.44  ipcrm: permission denied for id (1231061052)
% 0.21/0.44  ipcrm: permission denied for id (1231093821)
% 0.21/0.44  ipcrm: permission denied for id (1231126590)
% 0.21/0.44  ipcrm: permission denied for id (1225818175)
% 0.21/0.44  ipcrm: permission denied for id (1231159360)
% 0.21/0.44  ipcrm: permission denied for id (1225850945)
% 0.21/0.45  ipcrm: permission denied for id (1228406853)
% 0.21/0.45  ipcrm: permission denied for id (1231290438)
% 0.21/0.45  ipcrm: permission denied for id (1228472391)
% 0.21/0.45  ipcrm: permission denied for id (1231323208)
% 0.21/0.45  ipcrm: permission denied for id (1231355977)
% 0.21/0.45  ipcrm: permission denied for id (1228570698)
% 0.21/0.46  ipcrm: permission denied for id (1231454285)
% 0.21/0.46  ipcrm: permission denied for id (1228701774)
% 0.21/0.46  ipcrm: permission denied for id (1228734543)
% 0.21/0.46  ipcrm: permission denied for id (1228800081)
% 0.21/0.46  ipcrm: permission denied for id (1231552595)
% 0.21/0.47  ipcrm: permission denied for id (1225982036)
% 0.21/0.47  ipcrm: permission denied for id (1231585365)
% 0.21/0.47  ipcrm: permission denied for id (1231618134)
% 0.21/0.47  ipcrm: permission denied for id (1228963927)
% 0.21/0.47  ipcrm: permission denied for id (1228996696)
% 0.21/0.47  ipcrm: permission denied for id (1229029465)
% 0.21/0.47  ipcrm: permission denied for id (1229062234)
% 0.21/0.47  ipcrm: permission denied for id (1229095003)
% 0.21/0.48  ipcrm: permission denied for id (1231650908)
% 0.21/0.48  ipcrm: permission denied for id (1229226079)
% 0.21/0.48  ipcrm: permission denied for id (1231781985)
% 0.21/0.48  ipcrm: permission denied for id (1229357155)
% 0.21/0.49  ipcrm: permission denied for id (1229389924)
% 0.21/0.49  ipcrm: permission denied for id (1231913063)
% 0.21/0.49  ipcrm: permission denied for id (1231945832)
% 0.21/0.49  ipcrm: permission denied for id (1229553769)
% 0.21/0.49  ipcrm: permission denied for id (1229586538)
% 0.21/0.49  ipcrm: permission denied for id (1226178667)
% 0.21/0.50  ipcrm: permission denied for id (1229619308)
% 0.21/0.50  ipcrm: permission denied for id (1229684846)
% 0.21/0.50  ipcrm: permission denied for id (1229717615)
% 0.21/0.50  ipcrm: permission denied for id (1226244208)
% 0.21/0.50  ipcrm: permission denied for id (1226276977)
% 0.21/0.50  ipcrm: permission denied for id (1229750386)
% 0.21/0.50  ipcrm: permission denied for id (1229783155)
% 0.21/0.50  ipcrm: permission denied for id (1226342516)
% 0.21/0.51  ipcrm: permission denied for id (1232011381)
% 0.21/0.51  ipcrm: permission denied for id (1229914232)
% 0.21/0.51  ipcrm: permission denied for id (1229947001)
% 0.21/0.51  ipcrm: permission denied for id (1230012539)
% 0.21/0.51  ipcrm: permission denied for id (1230045308)
% 0.21/0.52  ipcrm: permission denied for id (1226440829)
% 0.21/0.52  ipcrm: permission denied for id (1226473599)
% 0.92/0.62  % (23863)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.92/0.62  % (23878)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.92/0.63  % (23863)Refutation found. Thanks to Tanya!
% 0.92/0.63  % SZS status Theorem for theBenchmark
% 0.92/0.63  % (23862)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.92/0.63  % SZS output start Proof for theBenchmark
% 0.92/0.63  fof(f60,plain,(
% 0.92/0.63    $false),
% 0.92/0.63    inference(subsumption_resolution,[],[f59,f23])).
% 0.92/0.63  fof(f23,plain,(
% 0.92/0.63    r2_hidden(sK2,sK0)),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f17,plain,(
% 0.92/0.63    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.92/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f16])).
% 0.92/0.63  fof(f16,plain,(
% 0.92/0.63    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.92/0.63    introduced(choice_axiom,[])).
% 0.92/0.63  fof(f9,plain,(
% 0.92/0.63    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.92/0.63    inference(flattening,[],[f8])).
% 0.92/0.63  fof(f8,plain,(
% 0.92/0.63    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.92/0.63    inference(ennf_transformation,[],[f7])).
% 0.92/0.63  fof(f7,negated_conjecture,(
% 0.92/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.92/0.63    inference(negated_conjecture,[],[f6])).
% 0.92/0.63  fof(f6,conjecture,(
% 0.92/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.92/0.63  fof(f59,plain,(
% 0.92/0.63    ~r2_hidden(sK2,sK0)),
% 0.92/0.63    inference(backward_demodulation,[],[f51,f58])).
% 0.92/0.63  fof(f58,plain,(
% 0.92/0.63    sK0 = k1_relat_1(sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f56,f21])).
% 0.92/0.63  fof(f21,plain,(
% 0.92/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f56,plain,(
% 0.92/0.63    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.92/0.63    inference(superposition,[],[f55,f30])).
% 0.92/0.63  fof(f30,plain,(
% 0.92/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.92/0.63    inference(cnf_transformation,[],[f13])).
% 0.92/0.63  fof(f13,plain,(
% 0.92/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.63    inference(ennf_transformation,[],[f4])).
% 0.92/0.63  fof(f4,axiom,(
% 0.92/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.92/0.63  fof(f55,plain,(
% 0.92/0.63    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f54,f24])).
% 0.92/0.63  fof(f24,plain,(
% 0.92/0.63    k1_xboole_0 != sK1),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f54,plain,(
% 0.92/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f53,f20])).
% 0.92/0.63  fof(f20,plain,(
% 0.92/0.63    v1_funct_2(sK3,sK0,sK1)),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f53,plain,(
% 0.92/0.63    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.92/0.63    inference(resolution,[],[f31,f21])).
% 0.92/0.63  fof(f31,plain,(
% 0.92/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.92/0.63    inference(cnf_transformation,[],[f18])).
% 0.92/0.63  fof(f18,plain,(
% 0.92/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.63    inference(nnf_transformation,[],[f15])).
% 0.92/0.63  fof(f15,plain,(
% 0.92/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.63    inference(flattening,[],[f14])).
% 0.92/0.63  fof(f14,plain,(
% 0.92/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.92/0.63    inference(ennf_transformation,[],[f5])).
% 0.92/0.63  fof(f5,axiom,(
% 0.92/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.92/0.63  fof(f51,plain,(
% 0.92/0.63    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.92/0.63    inference(subsumption_resolution,[],[f50,f43])).
% 0.92/0.63  fof(f43,plain,(
% 0.92/0.63    v1_relat_1(sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f42,f27])).
% 0.92/0.63  fof(f27,plain,(
% 0.92/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.92/0.63    inference(cnf_transformation,[],[f2])).
% 0.92/0.63  fof(f2,axiom,(
% 0.92/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.92/0.63  fof(f42,plain,(
% 0.92/0.63    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.92/0.63    inference(resolution,[],[f26,f21])).
% 0.92/0.63  fof(f26,plain,(
% 0.92/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.92/0.63    inference(cnf_transformation,[],[f10])).
% 0.92/0.63  fof(f10,plain,(
% 0.92/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.92/0.63    inference(ennf_transformation,[],[f1])).
% 0.92/0.63  fof(f1,axiom,(
% 0.92/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.92/0.63  fof(f50,plain,(
% 0.92/0.63    ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f49,f19])).
% 0.92/0.63  fof(f19,plain,(
% 0.92/0.63    v1_funct_1(sK3)),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f49,plain,(
% 0.92/0.63    ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.92/0.63    inference(subsumption_resolution,[],[f48,f22])).
% 0.92/0.63  fof(f22,plain,(
% 0.92/0.63    v2_funct_1(sK3)),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  fof(f48,plain,(
% 0.92/0.63    ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.92/0.63    inference(trivial_inequality_removal,[],[f47])).
% 0.92/0.63  fof(f47,plain,(
% 0.92/0.63    sK2 != sK2 | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.92/0.63    inference(superposition,[],[f25,f28])).
% 0.92/0.63  fof(f28,plain,(
% 0.92/0.63    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.92/0.63    inference(cnf_transformation,[],[f12])).
% 0.92/0.63  fof(f12,plain,(
% 0.92/0.63    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.92/0.63    inference(flattening,[],[f11])).
% 0.92/0.63  fof(f11,plain,(
% 0.92/0.63    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.92/0.63    inference(ennf_transformation,[],[f3])).
% 0.92/0.63  fof(f3,axiom,(
% 0.92/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.92/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.92/0.63  fof(f25,plain,(
% 0.92/0.63    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))),
% 0.92/0.63    inference(cnf_transformation,[],[f17])).
% 0.92/0.63  % SZS output end Proof for theBenchmark
% 0.92/0.63  % (23863)------------------------------
% 0.92/0.63  % (23863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.92/0.63  % (23863)Termination reason: Refutation
% 0.92/0.63  
% 0.92/0.63  % (23863)Memory used [KB]: 10618
% 0.92/0.63  % (23863)Time elapsed: 0.071 s
% 0.92/0.63  % (23863)------------------------------
% 0.92/0.63  % (23863)------------------------------
% 0.92/0.63  % (23724)Success in time 0.275 s
%------------------------------------------------------------------------------
