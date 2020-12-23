%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:01 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 137 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   18
%              Number of atoms          :  197 ( 511 expanded)
%              Number of equality atoms :   50 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195,f103])).

fof(f103,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f102,f18])).

fof(f18,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f102,plain,
    ( ~ v1_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f89,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f19,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f195,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f193,f17])).

fof(f193,plain,
    ( ~ v1_relat_1(sK0)
    | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(resolution,[],[f191,f18])).

fof(f191,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f190,f18])).

fof(f190,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f17])).

fof(f184,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f166,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK0))
      | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(backward_demodulation,[],[f115,f165])).

fof(f165,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f164,f18])).

fof(f164,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f158,f17])).

fof(f158,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f108,f22])).

fof(f108,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f87,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f66,f17])).

fof(f66,plain,
    ( ~ v1_relat_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f106,f18])).

fof(f106,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f95,f17])).

fof(f95,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f19,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = k2_relat_1(X0)
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k5_relat_1(k2_funct_1(sK0),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f109,f87])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k5_relat_1(k2_funct_1(sK0),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0))) ) ),
    inference(resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f20,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (803831809)
% 0.14/0.37  ipcrm: permission denied for id (803864578)
% 0.14/0.37  ipcrm: permission denied for id (809402371)
% 0.14/0.37  ipcrm: permission denied for id (803930116)
% 0.14/0.37  ipcrm: permission denied for id (803995654)
% 0.14/0.37  ipcrm: permission denied for id (809467911)
% 0.14/0.37  ipcrm: permission denied for id (809500680)
% 0.14/0.38  ipcrm: permission denied for id (804028425)
% 0.14/0.38  ipcrm: permission denied for id (804061194)
% 0.14/0.38  ipcrm: permission denied for id (809533451)
% 0.14/0.38  ipcrm: permission denied for id (806420492)
% 0.14/0.38  ipcrm: permission denied for id (804159501)
% 0.14/0.38  ipcrm: permission denied for id (806453262)
% 0.14/0.38  ipcrm: permission denied for id (806486031)
% 0.14/0.38  ipcrm: permission denied for id (809566224)
% 0.14/0.39  ipcrm: permission denied for id (804225041)
% 0.14/0.39  ipcrm: permission denied for id (806551570)
% 0.14/0.39  ipcrm: permission denied for id (804257811)
% 0.14/0.39  ipcrm: permission denied for id (806617109)
% 0.14/0.39  ipcrm: permission denied for id (806649878)
% 0.14/0.39  ipcrm: permission denied for id (804323351)
% 0.21/0.39  ipcrm: permission denied for id (806682648)
% 0.21/0.40  ipcrm: permission denied for id (806715417)
% 0.21/0.40  ipcrm: permission denied for id (806748186)
% 0.21/0.40  ipcrm: permission denied for id (804421659)
% 0.21/0.40  ipcrm: permission denied for id (804454428)
% 0.21/0.40  ipcrm: permission denied for id (804487197)
% 0.21/0.40  ipcrm: permission denied for id (804519967)
% 0.21/0.40  ipcrm: permission denied for id (804552736)
% 0.21/0.41  ipcrm: permission denied for id (809664545)
% 0.21/0.41  ipcrm: permission denied for id (809697314)
% 0.21/0.41  ipcrm: permission denied for id (806944805)
% 0.21/0.42  ipcrm: permission denied for id (809861160)
% 0.21/0.42  ipcrm: permission denied for id (809926698)
% 0.21/0.42  ipcrm: permission denied for id (807141419)
% 0.21/0.42  ipcrm: permission denied for id (809992237)
% 0.21/0.42  ipcrm: permission denied for id (804618286)
% 0.21/0.42  ipcrm: permission denied for id (807239727)
% 0.21/0.43  ipcrm: permission denied for id (804651056)
% 0.21/0.43  ipcrm: permission denied for id (804683826)
% 0.21/0.43  ipcrm: permission denied for id (807305267)
% 0.21/0.43  ipcrm: permission denied for id (807338036)
% 0.21/0.43  ipcrm: permission denied for id (810090550)
% 0.21/0.43  ipcrm: permission denied for id (804847671)
% 0.21/0.44  ipcrm: permission denied for id (807436344)
% 0.21/0.44  ipcrm: permission denied for id (807469113)
% 0.21/0.44  ipcrm: permission denied for id (810123322)
% 0.21/0.44  ipcrm: permission denied for id (807534651)
% 0.21/0.44  ipcrm: permission denied for id (807567420)
% 0.21/0.44  ipcrm: permission denied for id (804945981)
% 0.21/0.44  ipcrm: permission denied for id (807600190)
% 0.21/0.45  ipcrm: permission denied for id (804978751)
% 0.21/0.45  ipcrm: permission denied for id (807632960)
% 0.21/0.45  ipcrm: permission denied for id (810188866)
% 0.21/0.45  ipcrm: permission denied for id (810221635)
% 0.21/0.45  ipcrm: permission denied for id (807764036)
% 0.21/0.45  ipcrm: permission denied for id (805109829)
% 0.21/0.45  ipcrm: permission denied for id (807796806)
% 0.21/0.46  ipcrm: permission denied for id (807829575)
% 0.21/0.46  ipcrm: permission denied for id (807862344)
% 0.21/0.46  ipcrm: permission denied for id (805240905)
% 0.21/0.46  ipcrm: permission denied for id (810254410)
% 0.21/0.46  ipcrm: permission denied for id (810319948)
% 0.21/0.47  ipcrm: permission denied for id (808058959)
% 0.21/0.47  ipcrm: permission denied for id (810418256)
% 0.21/0.47  ipcrm: permission denied for id (805404753)
% 0.21/0.47  ipcrm: permission denied for id (808124498)
% 0.21/0.47  ipcrm: permission denied for id (808157267)
% 0.21/0.47  ipcrm: permission denied for id (805437524)
% 0.21/0.47  ipcrm: permission denied for id (808190037)
% 0.21/0.47  ipcrm: permission denied for id (808222806)
% 0.21/0.48  ipcrm: permission denied for id (808288344)
% 0.21/0.48  ipcrm: permission denied for id (808419419)
% 0.21/0.48  ipcrm: permission denied for id (808452188)
% 0.21/0.48  ipcrm: permission denied for id (808484957)
% 0.21/0.48  ipcrm: permission denied for id (808517726)
% 0.21/0.49  ipcrm: permission denied for id (808550495)
% 0.21/0.49  ipcrm: permission denied for id (805634145)
% 0.21/0.49  ipcrm: permission denied for id (808616034)
% 0.21/0.49  ipcrm: permission denied for id (810582115)
% 0.21/0.49  ipcrm: permission denied for id (810614884)
% 0.21/0.49  ipcrm: permission denied for id (810647653)
% 0.21/0.50  ipcrm: permission denied for id (805732454)
% 0.21/0.50  ipcrm: permission denied for id (810680423)
% 0.21/0.50  ipcrm: permission denied for id (810713192)
% 0.21/0.50  ipcrm: permission denied for id (808845417)
% 0.21/0.50  ipcrm: permission denied for id (810745962)
% 0.21/0.50  ipcrm: permission denied for id (808910955)
% 0.21/0.50  ipcrm: permission denied for id (805830764)
% 0.21/0.51  ipcrm: permission denied for id (805863533)
% 0.21/0.51  ipcrm: permission denied for id (808943726)
% 0.21/0.51  ipcrm: permission denied for id (805896303)
% 0.21/0.51  ipcrm: permission denied for id (805929072)
% 0.21/0.51  ipcrm: permission denied for id (808976497)
% 0.34/0.51  ipcrm: permission denied for id (809074803)
% 0.34/0.51  ipcrm: permission denied for id (805994612)
% 0.34/0.52  ipcrm: permission denied for id (806027381)
% 0.34/0.52  ipcrm: permission denied for id (809107574)
% 0.34/0.52  ipcrm: permission denied for id (806092919)
% 0.34/0.52  ipcrm: permission denied for id (806125688)
% 0.34/0.52  ipcrm: permission denied for id (809173114)
% 0.34/0.52  ipcrm: permission denied for id (810844283)
% 0.37/0.53  ipcrm: permission denied for id (806191231)
% 0.37/0.62  % (10846)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.37/0.62  % (10838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.37/0.62  % (10846)Refutation found. Thanks to Tanya!
% 0.37/0.62  % SZS status Theorem for theBenchmark
% 0.38/0.63  % SZS output start Proof for theBenchmark
% 0.38/0.63  fof(f196,plain,(
% 0.38/0.63    $false),
% 0.38/0.63    inference(subsumption_resolution,[],[f195,f103])).
% 0.38/0.63  fof(f103,plain,(
% 0.38/0.63    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f102,f18])).
% 0.38/0.63  fof(f18,plain,(
% 0.38/0.63    v1_funct_1(sK0)),
% 0.38/0.63    inference(cnf_transformation,[],[f8])).
% 0.38/0.63  fof(f8,plain,(
% 0.38/0.63    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.38/0.63    inference(flattening,[],[f7])).
% 0.38/0.63  fof(f7,plain,(
% 0.38/0.63    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.38/0.63    inference(ennf_transformation,[],[f6])).
% 0.38/0.63  fof(f6,negated_conjecture,(
% 0.38/0.63    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.38/0.63    inference(negated_conjecture,[],[f5])).
% 0.38/0.63  fof(f5,conjecture,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.38/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).
% 0.38/0.63  fof(f102,plain,(
% 0.38/0.63    ~v1_funct_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f89,f17])).
% 0.38/0.63  fof(f17,plain,(
% 0.38/0.63    v1_relat_1(sK0)),
% 0.38/0.63    inference(cnf_transformation,[],[f8])).
% 0.38/0.63  fof(f89,plain,(
% 0.38/0.63    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.38/0.63    inference(resolution,[],[f19,f24])).
% 0.38/0.63  fof(f24,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.38/0.63    inference(cnf_transformation,[],[f12])).
% 0.38/0.63  fof(f12,plain,(
% 0.38/0.63    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.38/0.63    inference(flattening,[],[f11])).
% 0.38/0.63  fof(f11,plain,(
% 0.38/0.63    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.38/0.63    inference(ennf_transformation,[],[f4])).
% 0.38/0.63  fof(f4,axiom,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.38/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.38/0.63  fof(f19,plain,(
% 0.38/0.63    v2_funct_1(sK0)),
% 0.38/0.63    inference(cnf_transformation,[],[f8])).
% 0.38/0.63  fof(f195,plain,(
% 0.38/0.63    k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f193,f17])).
% 0.38/0.63  fof(f193,plain,(
% 0.38/0.63    ~v1_relat_1(sK0) | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))),
% 0.38/0.63    inference(resolution,[],[f191,f18])).
% 0.38/0.63  fof(f191,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0)) )),
% 0.38/0.63    inference(subsumption_resolution,[],[f190,f18])).
% 0.38/0.63  fof(f190,plain,(
% 0.38/0.63    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_funct_1(sK0)) )),
% 0.38/0.63    inference(subsumption_resolution,[],[f184,f17])).
% 0.38/0.63  fof(f184,plain,(
% 0.38/0.63    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)) )),
% 0.38/0.63    inference(resolution,[],[f166,f22])).
% 0.38/0.63  fof(f22,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.38/0.63    inference(cnf_transformation,[],[f10])).
% 0.38/0.63  fof(f10,plain,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.38/0.63    inference(flattening,[],[f9])).
% 0.38/0.63  fof(f9,plain,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.38/0.63    inference(ennf_transformation,[],[f1])).
% 0.38/0.63  fof(f1,axiom,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.38/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.38/0.63  fof(f166,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(k2_funct_1(sK0),X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.38/0.63    inference(backward_demodulation,[],[f115,f165])).
% 0.38/0.63  fof(f165,plain,(
% 0.38/0.63    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f164,f18])).
% 0.38/0.63  fof(f164,plain,(
% 0.38/0.63    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.38/0.63    inference(subsumption_resolution,[],[f158,f17])).
% 0.38/0.63  fof(f158,plain,(
% 0.38/0.63    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.38/0.63    inference(resolution,[],[f108,f22])).
% 0.38/0.63  fof(f108,plain,(
% 0.38/0.63    ~v1_funct_1(k2_funct_1(sK0)) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f107,f87])).
% 0.38/0.63  fof(f87,plain,(
% 0.38/0.63    v1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f66,f17])).
% 0.38/0.63  fof(f66,plain,(
% 0.38/0.63    ~v1_relat_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(resolution,[],[f18,f21])).
% 0.38/0.63  fof(f21,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.38/0.63    inference(cnf_transformation,[],[f10])).
% 0.38/0.63  fof(f107,plain,(
% 0.38/0.63    ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f106,f18])).
% 0.38/0.63  fof(f106,plain,(
% 0.38/0.63    ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(subsumption_resolution,[],[f95,f17])).
% 0.38/0.63  fof(f95,plain,(
% 0.38/0.63    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(resolution,[],[f19,f36])).
% 0.38/0.63  fof(f36,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.38/0.63    inference(equality_resolution,[],[f34])).
% 0.38/0.63  fof(f34,plain,(
% 0.38/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) = k2_relat_1(X0) | k2_funct_1(X0) != X1) )),
% 0.38/0.63    inference(cnf_transformation,[],[f14])).
% 0.38/0.63  fof(f14,plain,(
% 0.38/0.63    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.38/0.63    inference(flattening,[],[f13])).
% 0.38/0.63  fof(f13,plain,(
% 0.38/0.63    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.38/0.63    inference(ennf_transformation,[],[f3])).
% 0.38/0.63  fof(f3,axiom,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.38/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.38/0.63  fof(f115,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k5_relat_1(k2_funct_1(sK0),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))) )),
% 0.38/0.63    inference(subsumption_resolution,[],[f109,f87])).
% 0.38/0.63  fof(f109,plain,(
% 0.38/0.63    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k5_relat_1(k2_funct_1(sK0),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))) )),
% 0.38/0.63    inference(resolution,[],[f20,f35])).
% 0.38/0.63  fof(f35,plain,(
% 0.38/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.38/0.63    inference(cnf_transformation,[],[f16])).
% 0.38/0.63  fof(f16,plain,(
% 0.38/0.63    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.38/0.63    inference(flattening,[],[f15])).
% 0.38/0.63  fof(f15,plain,(
% 0.38/0.63    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.38/0.63    inference(ennf_transformation,[],[f2])).
% 0.38/0.63  fof(f2,axiom,(
% 0.38/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.38/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.38/0.63  fof(f20,plain,(
% 0.38/0.63    ~v2_funct_1(k2_funct_1(sK0))),
% 0.38/0.63    inference(cnf_transformation,[],[f8])).
% 0.38/0.63  % SZS output end Proof for theBenchmark
% 0.38/0.63  % (10846)------------------------------
% 0.38/0.63  % (10846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.63  % (10846)Termination reason: Refutation
% 0.38/0.63  
% 0.38/0.63  % (10846)Memory used [KB]: 1663
% 0.38/0.63  % (10846)Time elapsed: 0.050 s
% 0.38/0.63  % (10846)------------------------------
% 0.38/0.63  % (10846)------------------------------
% 0.38/0.63  % (10601)Success in time 0.271 s
%------------------------------------------------------------------------------
