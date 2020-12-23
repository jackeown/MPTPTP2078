%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 10.63s
% Output     : CNFRefutation 10.87s
% Verified   : 
% Statistics : Number of formulae       :  208 (4087 expanded)
%              Number of leaves         :   55 (1473 expanded)
%              Depth                    :   26
%              Number of atoms          :  596 (12112 expanded)
%              Number of equality atoms :   29 (1799 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_168,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_180,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_176,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_193,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(c_88,plain,(
    k3_yellow_0(k2_yellow_1('#skF_7')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_70,plain,(
    ! [A_69] : l1_orders_2(k2_yellow_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_80,plain,(
    ! [A_71] : u1_struct_0(k2_yellow_1(A_71)) = A_71 ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_144,plain,(
    ! [A_94] :
      ( m1_subset_1(k3_yellow_0(A_94),u1_struct_0(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_147,plain,(
    ! [A_71] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(A_71)),A_71)
      | ~ l1_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_144])).

tff(c_149,plain,(
    ! [A_71] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_71)),A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_147])).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    r2_hidden(k1_xboole_0,'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_130,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(A_90,B_91)
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    m1_subset_1(k1_xboole_0,'#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_130])).

tff(c_165,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_2'(A_98,B_99),A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_98,B_99] :
      ( ~ v1_xboole_0(A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_74,plain,(
    ! [A_70] : v3_orders_2(k2_yellow_1(A_70)) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_84,plain,(
    ! [A_72,B_76,C_78] :
      ( r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ r1_tarski(B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k2_yellow_1(A_72)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_72)))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_94,plain,(
    ! [A_72,B_76,C_78] :
      ( r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ r1_tarski(B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_84])).

tff(c_1203,plain,(
    ! [A_334,B_335,C_336] :
      ( r1_orders_2(A_334,B_335,C_336)
      | ~ r3_orders_2(A_334,B_335,C_336)
      | ~ m1_subset_1(C_336,u1_struct_0(A_334))
      | ~ m1_subset_1(B_335,u1_struct_0(A_334))
      | ~ l1_orders_2(A_334)
      | ~ v3_orders_2(A_334)
      | v2_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1207,plain,(
    ! [A_72,B_76,C_78] :
      ( r1_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k2_yellow_1(A_72)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_72)))
      | ~ l1_orders_2(k2_yellow_1(A_72))
      | ~ v3_orders_2(k2_yellow_1(A_72))
      | v2_struct_0(k2_yellow_1(A_72))
      | ~ r1_tarski(B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_94,c_1203])).

tff(c_1213,plain,(
    ! [A_72,B_76,C_78] :
      ( r1_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | v2_struct_0(k2_yellow_1(A_72))
      | ~ r1_tarski(B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_80,c_80,c_1207])).

tff(c_78,plain,(
    ! [A_70] : v5_orders_2(k2_yellow_1(A_70)) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1214,plain,(
    ! [A_337,B_338,C_339] :
      ( r1_orders_2(k2_yellow_1(A_337),B_338,C_339)
      | v2_struct_0(k2_yellow_1(A_337))
      | ~ r1_tarski(B_338,C_339)
      | ~ m1_subset_1(C_339,A_337)
      | ~ m1_subset_1(B_338,A_337)
      | v1_xboole_0(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_80,c_80,c_1207])).

tff(c_24,plain,(
    ! [C_23,B_21,A_17] :
      ( C_23 = B_21
      | ~ r1_orders_2(A_17,C_23,B_21)
      | ~ r1_orders_2(A_17,B_21,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_17))
      | ~ m1_subset_1(B_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v5_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1220,plain,(
    ! [C_339,B_338,A_337] :
      ( C_339 = B_338
      | ~ r1_orders_2(k2_yellow_1(A_337),C_339,B_338)
      | ~ m1_subset_1(B_338,u1_struct_0(k2_yellow_1(A_337)))
      | ~ m1_subset_1(C_339,u1_struct_0(k2_yellow_1(A_337)))
      | ~ l1_orders_2(k2_yellow_1(A_337))
      | ~ v5_orders_2(k2_yellow_1(A_337))
      | v2_struct_0(k2_yellow_1(A_337))
      | ~ r1_tarski(B_338,C_339)
      | ~ m1_subset_1(C_339,A_337)
      | ~ m1_subset_1(B_338,A_337)
      | v1_xboole_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_1214,c_24])).

tff(c_1849,plain,(
    ! [C_398,B_399,A_400] :
      ( C_398 = B_399
      | ~ r1_orders_2(k2_yellow_1(A_400),C_398,B_399)
      | v2_struct_0(k2_yellow_1(A_400))
      | ~ r1_tarski(B_399,C_398)
      | ~ m1_subset_1(C_398,A_400)
      | ~ m1_subset_1(B_399,A_400)
      | v1_xboole_0(A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_70,c_80,c_80,c_1220])).

tff(c_2001,plain,(
    ! [C_403,B_404,A_405] :
      ( C_403 = B_404
      | ~ r1_tarski(C_403,B_404)
      | v2_struct_0(k2_yellow_1(A_405))
      | ~ r1_tarski(B_404,C_403)
      | ~ m1_subset_1(C_403,A_405)
      | ~ m1_subset_1(B_404,A_405)
      | v1_xboole_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_1213,c_1849])).

tff(c_2014,plain,(
    ! [B_406,A_407,A_408] :
      ( B_406 = A_407
      | v2_struct_0(k2_yellow_1(A_408))
      | ~ r1_tarski(B_406,A_407)
      | ~ m1_subset_1(A_407,A_408)
      | ~ m1_subset_1(B_406,A_408)
      | v1_xboole_0(A_408)
      | ~ v1_xboole_0(A_407) ) ),
    inference(resolution,[status(thm)],[c_173,c_2001])).

tff(c_2025,plain,(
    ! [B_409,A_410,A_411] :
      ( B_409 = A_410
      | v2_struct_0(k2_yellow_1(A_411))
      | ~ m1_subset_1(B_409,A_411)
      | ~ m1_subset_1(A_410,A_411)
      | v1_xboole_0(A_411)
      | ~ v1_xboole_0(B_409)
      | ~ v1_xboole_0(A_410) ) ),
    inference(resolution,[status(thm)],[c_173,c_2014])).

tff(c_2065,plain,(
    ! [A_410] :
      ( k1_xboole_0 = A_410
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ m1_subset_1(A_410,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_410) ) ),
    inference(resolution,[status(thm)],[c_138,c_2025])).

tff(c_2087,plain,(
    ! [A_410] :
      ( k1_xboole_0 = A_410
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ m1_subset_1(A_410,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ v1_xboole_0(A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2065])).

tff(c_2088,plain,(
    ! [A_410] :
      ( k1_xboole_0 = A_410
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ m1_subset_1(A_410,'#skF_7')
      | ~ v1_xboole_0(A_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2087])).

tff(c_2089,plain,(
    v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2088])).

tff(c_139,plain,(
    ! [A_92] :
      ( v1_xboole_0(u1_struct_0(A_92))
      | ~ l1_struct_0(A_92)
      | ~ v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,(
    ! [A_71] :
      ( v1_xboole_0(A_71)
      | ~ l1_struct_0(k2_yellow_1(A_71))
      | ~ v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_139])).

tff(c_2095,plain,
    ( v1_xboole_0('#skF_7')
    | ~ l1_struct_0(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2089,c_142])).

tff(c_2102,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2095])).

tff(c_2117,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_18,c_2102])).

tff(c_2121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2117])).

tff(c_2123,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2088])).

tff(c_251,plain,(
    ! [A_119] :
      ( r1_lattice3(A_119,u1_struct_0(A_119),'#skF_5'(A_119))
      | ~ v1_yellow_0(A_119)
      | ~ l1_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_254,plain,(
    ! [A_71] :
      ( r1_lattice3(k2_yellow_1(A_71),A_71,'#skF_5'(k2_yellow_1(A_71)))
      | ~ v1_yellow_0(k2_yellow_1(A_71))
      | ~ l1_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_251])).

tff(c_256,plain,(
    ! [A_71] :
      ( r1_lattice3(k2_yellow_1(A_71),A_71,'#skF_5'(k2_yellow_1(A_71)))
      | ~ v1_yellow_0(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_254])).

tff(c_720,plain,(
    ! [A_237,C_238,D_239,B_240] :
      ( r1_orders_2(A_237,C_238,D_239)
      | ~ r2_hidden(D_239,B_240)
      | ~ m1_subset_1(D_239,u1_struct_0(A_237))
      | ~ r1_lattice3(A_237,B_240,C_238)
      | ~ m1_subset_1(C_238,u1_struct_0(A_237))
      | ~ l1_orders_2(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_900,plain,(
    ! [A_289,C_290] :
      ( r1_orders_2(A_289,C_290,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_289))
      | ~ r1_lattice3(A_289,'#skF_7',C_290)
      | ~ m1_subset_1(C_290,u1_struct_0(A_289))
      | ~ l1_orders_2(A_289) ) ),
    inference(resolution,[status(thm)],[c_90,c_720])).

tff(c_902,plain,(
    ! [A_71,C_290] :
      ( r1_orders_2(k2_yellow_1(A_71),C_290,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_71)
      | ~ r1_lattice3(k2_yellow_1(A_71),'#skF_7',C_290)
      | ~ m1_subset_1(C_290,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_900])).

tff(c_904,plain,(
    ! [A_71,C_290] :
      ( r1_orders_2(k2_yellow_1(A_71),C_290,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_71)
      | ~ r1_lattice3(k2_yellow_1(A_71),'#skF_7',C_290)
      | ~ m1_subset_1(C_290,A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80,c_902])).

tff(c_1045,plain,(
    ! [A_299,B_300,C_301] :
      ( r3_orders_2(A_299,B_300,C_301)
      | ~ r1_orders_2(A_299,B_300,C_301)
      | ~ m1_subset_1(C_301,u1_struct_0(A_299))
      | ~ m1_subset_1(B_300,u1_struct_0(A_299))
      | ~ l1_orders_2(A_299)
      | ~ v3_orders_2(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1090,plain,(
    ! [A_71,B_300,C_301] :
      ( r3_orders_2(k2_yellow_1(A_71),B_300,C_301)
      | ~ r1_orders_2(k2_yellow_1(A_71),B_300,C_301)
      | ~ m1_subset_1(C_301,A_71)
      | ~ m1_subset_1(B_300,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v3_orders_2(k2_yellow_1(A_71))
      | v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1045])).

tff(c_1173,plain,(
    ! [A_323,B_324,C_325] :
      ( r3_orders_2(k2_yellow_1(A_323),B_324,C_325)
      | ~ r1_orders_2(k2_yellow_1(A_323),B_324,C_325)
      | ~ m1_subset_1(C_325,A_323)
      | ~ m1_subset_1(B_324,A_323)
      | v2_struct_0(k2_yellow_1(A_323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_80,c_1090])).

tff(c_86,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k2_yellow_1(A_72)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_72)))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_93,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_86])).

tff(c_1312,plain,(
    ! [B_367,C_368,A_369] :
      ( r1_tarski(B_367,C_368)
      | v1_xboole_0(A_369)
      | ~ r1_orders_2(k2_yellow_1(A_369),B_367,C_368)
      | ~ m1_subset_1(C_368,A_369)
      | ~ m1_subset_1(B_367,A_369)
      | v2_struct_0(k2_yellow_1(A_369)) ) ),
    inference(resolution,[status(thm)],[c_1173,c_93])).

tff(c_1518,plain,(
    ! [C_379,A_380] :
      ( r1_tarski(C_379,k1_xboole_0)
      | v1_xboole_0(A_380)
      | v2_struct_0(k2_yellow_1(A_380))
      | ~ m1_subset_1(k1_xboole_0,A_380)
      | ~ r1_lattice3(k2_yellow_1(A_380),'#skF_7',C_379)
      | ~ m1_subset_1(C_379,A_380) ) ),
    inference(resolution,[status(thm)],[c_904,c_1312])).

tff(c_1594,plain,
    ( r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0)
    | v1_xboole_0('#skF_7')
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | ~ m1_subset_1(k1_xboole_0,'#skF_7')
    | ~ m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7')
    | ~ v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_256,c_1518])).

tff(c_1643,plain,
    ( r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0)
    | v1_xboole_0('#skF_7')
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | ~ m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7')
    | ~ v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1594])).

tff(c_1644,plain,
    ( r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0)
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | ~ m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7')
    | ~ v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1643])).

tff(c_1660,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1644])).

tff(c_418,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_hidden('#skF_3'(A_173,B_174,C_175),B_174)
      | r1_lattice3(A_173,B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_428,plain,(
    ! [A_173,B_174,C_175] :
      ( m1_subset_1('#skF_3'(A_173,B_174,C_175),B_174)
      | r1_lattice3(A_173,B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(resolution,[status(thm)],[c_418,c_14])).

tff(c_28,plain,(
    ! [A_24,C_32,B_31] :
      ( ~ r1_orders_2(A_24,C_32,'#skF_3'(A_24,B_31,C_32))
      | r1_lattice3(A_24,B_31,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1228,plain,(
    ! [A_337,B_31,B_338] :
      ( r1_lattice3(k2_yellow_1(A_337),B_31,B_338)
      | ~ m1_subset_1(B_338,u1_struct_0(k2_yellow_1(A_337)))
      | ~ l1_orders_2(k2_yellow_1(A_337))
      | v2_struct_0(k2_yellow_1(A_337))
      | ~ r1_tarski(B_338,'#skF_3'(k2_yellow_1(A_337),B_31,B_338))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_337),B_31,B_338),A_337)
      | ~ m1_subset_1(B_338,A_337)
      | v1_xboole_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_1214,c_28])).

tff(c_9536,plain,(
    ! [A_953,B_954,B_955] :
      ( r1_lattice3(k2_yellow_1(A_953),B_954,B_955)
      | v2_struct_0(k2_yellow_1(A_953))
      | ~ r1_tarski(B_955,'#skF_3'(k2_yellow_1(A_953),B_954,B_955))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_953),B_954,B_955),A_953)
      | ~ m1_subset_1(B_955,A_953)
      | v1_xboole_0(A_953) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80,c_1228])).

tff(c_9557,plain,(
    ! [A_956,B_957,A_958] :
      ( r1_lattice3(k2_yellow_1(A_956),B_957,A_958)
      | v2_struct_0(k2_yellow_1(A_956))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_956),B_957,A_958),A_956)
      | ~ m1_subset_1(A_958,A_956)
      | v1_xboole_0(A_956)
      | ~ v1_xboole_0(A_958) ) ),
    inference(resolution,[status(thm)],[c_173,c_9536])).

tff(c_9565,plain,(
    ! [B_174,C_175] :
      ( v2_struct_0(k2_yellow_1(B_174))
      | ~ m1_subset_1(C_175,B_174)
      | v1_xboole_0(B_174)
      | ~ v1_xboole_0(C_175)
      | r1_lattice3(k2_yellow_1(B_174),B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(k2_yellow_1(B_174)))
      | ~ l1_orders_2(k2_yellow_1(B_174)) ) ),
    inference(resolution,[status(thm)],[c_428,c_9557])).

tff(c_9576,plain,(
    ! [B_959,C_960] :
      ( v2_struct_0(k2_yellow_1(B_959))
      | v1_xboole_0(B_959)
      | ~ v1_xboole_0(C_960)
      | r1_lattice3(k2_yellow_1(B_959),B_959,C_960)
      | ~ m1_subset_1(C_960,B_959) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80,c_9565])).

tff(c_328,plain,(
    ! [A_145,B_146] :
      ( v1_yellow_0(A_145)
      | ~ r1_lattice3(A_145,u1_struct_0(A_145),B_146)
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_334,plain,(
    ! [A_71,B_146] :
      ( v1_yellow_0(k2_yellow_1(A_71))
      | ~ r1_lattice3(k2_yellow_1(A_71),A_71,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_328])).

tff(c_337,plain,(
    ! [A_71,B_146] :
      ( v1_yellow_0(k2_yellow_1(A_71))
      | ~ r1_lattice3(k2_yellow_1(A_71),A_71,B_146)
      | ~ m1_subset_1(B_146,A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80,c_334])).

tff(c_9657,plain,(
    ! [B_961,C_962] :
      ( v1_yellow_0(k2_yellow_1(B_961))
      | v2_struct_0(k2_yellow_1(B_961))
      | v1_xboole_0(B_961)
      | ~ v1_xboole_0(C_962)
      | ~ m1_subset_1(C_962,B_961) ) ),
    inference(resolution,[status(thm)],[c_9576,c_337])).

tff(c_9707,plain,
    ( v1_yellow_0(k2_yellow_1('#skF_7'))
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_138,c_9657])).

tff(c_9742,plain,
    ( v1_yellow_0(k2_yellow_1('#skF_7'))
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9707])).

tff(c_9744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2123,c_1660,c_9742])).

tff(c_9746,plain,(
    v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1644])).

tff(c_245,plain,(
    ! [A_118] :
      ( m1_subset_1('#skF_5'(A_118),u1_struct_0(A_118))
      | ~ v1_yellow_0(A_118)
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_248,plain,(
    ! [A_71] :
      ( m1_subset_1('#skF_5'(k2_yellow_1(A_71)),A_71)
      | ~ v1_yellow_0(k2_yellow_1(A_71))
      | ~ l1_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_245])).

tff(c_250,plain,(
    ! [A_71] :
      ( m1_subset_1('#skF_5'(k2_yellow_1(A_71)),A_71)
      | ~ v1_yellow_0(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_248])).

tff(c_9745,plain,
    ( ~ m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7')
    | v2_struct_0(k2_yellow_1('#skF_7'))
    | r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1644])).

tff(c_9747,plain,(
    ~ m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_9745])).

tff(c_9750,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_250,c_9747])).

tff(c_9754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9746,c_9750])).

tff(c_9755,plain,
    ( r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0)
    | v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9745])).

tff(c_9757,plain,(
    v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_9755])).

tff(c_9763,plain,
    ( v1_xboole_0('#skF_7')
    | ~ l1_struct_0(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9757,c_142])).

tff(c_9769,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_9763])).

tff(c_9787,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_18,c_9769])).

tff(c_9791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9787])).

tff(c_9793,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9755])).

tff(c_10637,plain,(
    ! [C_1031,B_1032,A_1033] :
      ( C_1031 = B_1032
      | ~ r1_orders_2(k2_yellow_1(A_1033),C_1031,B_1032)
      | v2_struct_0(k2_yellow_1(A_1033))
      | ~ r1_tarski(B_1032,C_1031)
      | ~ m1_subset_1(C_1031,A_1033)
      | ~ m1_subset_1(B_1032,A_1033)
      | v1_xboole_0(A_1033) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_70,c_80,c_80,c_1220])).

tff(c_10711,plain,(
    ! [C_1034,B_1035,A_1036] :
      ( C_1034 = B_1035
      | ~ r1_tarski(C_1034,B_1035)
      | v2_struct_0(k2_yellow_1(A_1036))
      | ~ r1_tarski(B_1035,C_1034)
      | ~ m1_subset_1(C_1034,A_1036)
      | ~ m1_subset_1(B_1035,A_1036)
      | v1_xboole_0(A_1036) ) ),
    inference(resolution,[status(thm)],[c_1213,c_10637])).

tff(c_10727,plain,(
    ! [B_1037,A_1038,A_1039] :
      ( B_1037 = A_1038
      | v2_struct_0(k2_yellow_1(A_1039))
      | ~ r1_tarski(B_1037,A_1038)
      | ~ m1_subset_1(A_1038,A_1039)
      | ~ m1_subset_1(B_1037,A_1039)
      | v1_xboole_0(A_1039)
      | ~ v1_xboole_0(A_1038) ) ),
    inference(resolution,[status(thm)],[c_173,c_10711])).

tff(c_10741,plain,(
    ! [B_1040,A_1041,A_1042] :
      ( B_1040 = A_1041
      | v2_struct_0(k2_yellow_1(A_1042))
      | ~ m1_subset_1(B_1040,A_1042)
      | ~ m1_subset_1(A_1041,A_1042)
      | v1_xboole_0(A_1042)
      | ~ v1_xboole_0(B_1040)
      | ~ v1_xboole_0(A_1041) ) ),
    inference(resolution,[status(thm)],[c_173,c_10727])).

tff(c_10783,plain,(
    ! [A_1041] :
      ( k1_xboole_0 = A_1041
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ m1_subset_1(A_1041,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_1041) ) ),
    inference(resolution,[status(thm)],[c_138,c_10741])).

tff(c_10809,plain,(
    ! [A_1041] :
      ( k1_xboole_0 = A_1041
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ m1_subset_1(A_1041,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ v1_xboole_0(A_1041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10783])).

tff(c_10827,plain,(
    ! [A_1046] :
      ( k1_xboole_0 = A_1046
      | ~ m1_subset_1(A_1046,'#skF_7')
      | ~ v1_xboole_0(A_1046) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_9793,c_10809])).

tff(c_10878,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_7')) = k1_xboole_0
    | ~ v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_149,c_10827])).

tff(c_10904,plain,(
    ~ v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10878])).

tff(c_66,plain,(
    ! [A_68] :
      ( r1_yellow_0(A_68,k1_xboole_0)
      | ~ l1_orders_2(A_68)
      | ~ v1_yellow_0(A_68)
      | ~ v5_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_9792,plain,(
    r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9755])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_199,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_258,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121),B_122)
      | ~ r1_tarski(A_121,B_122)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_269,plain,(
    ! [B_122,A_121] :
      ( ~ v1_xboole_0(B_122)
      | ~ r1_tarski(A_121,B_122)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_9808,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_9792,c_269])).

tff(c_9823,plain,(
    v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9808])).

tff(c_9756,plain,(
    m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_9745])).

tff(c_10830,plain,
    ( '#skF_5'(k2_yellow_1('#skF_7')) = k1_xboole_0
    | ~ v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_9756,c_10827])).

tff(c_10888,plain,(
    '#skF_5'(k2_yellow_1('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9823,c_10830])).

tff(c_48,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_5'(A_49),u1_struct_0(A_49))
      | ~ v1_yellow_0(A_49)
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_351,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_4'(A_156,B_157,C_158),B_157)
      | r2_lattice3(A_156,B_157,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1178,plain,(
    ! [A_326,B_327,C_328,B_329] :
      ( r2_hidden('#skF_4'(A_326,B_327,C_328),B_329)
      | ~ r1_tarski(B_327,B_329)
      | r2_lattice3(A_326,B_327,C_328)
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(resolution,[status(thm)],[c_351,c_6])).

tff(c_1195,plain,(
    ! [B_329,B_327,A_326,C_328] :
      ( ~ v1_xboole_0(B_329)
      | ~ r1_tarski(B_327,B_329)
      | r2_lattice3(A_326,B_327,C_328)
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(resolution,[status(thm)],[c_1178,c_2])).

tff(c_9795,plain,(
    ! [A_326,C_328] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_lattice3(A_326,'#skF_5'(k2_yellow_1('#skF_7')),C_328)
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(resolution,[status(thm)],[c_9792,c_1195])).

tff(c_9811,plain,(
    ! [A_326,C_328] :
      ( r2_lattice3(A_326,'#skF_5'(k2_yellow_1('#skF_7')),C_328)
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9795])).

tff(c_11436,plain,(
    ! [A_1074,C_1075] :
      ( r2_lattice3(A_1074,k1_xboole_0,C_1075)
      | ~ m1_subset_1(C_1075,u1_struct_0(A_1074))
      | ~ l1_orders_2(A_1074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10888,c_9811])).

tff(c_11597,plain,(
    ! [A_1088] :
      ( r2_lattice3(A_1088,k1_xboole_0,'#skF_5'(A_1088))
      | ~ v1_yellow_0(A_1088)
      | ~ l1_orders_2(A_1088) ) ),
    inference(resolution,[status(thm)],[c_48,c_11436])).

tff(c_11604,plain,
    ( r2_lattice3(k2_yellow_1('#skF_7'),k1_xboole_0,k1_xboole_0)
    | ~ v1_yellow_0(k2_yellow_1('#skF_7'))
    | ~ l1_orders_2(k2_yellow_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10888,c_11597])).

tff(c_11609,plain,(
    r2_lattice3(k2_yellow_1('#skF_7'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9746,c_11604])).

tff(c_150,plain,(
    ! [A_95] :
      ( k1_yellow_0(A_95,k1_xboole_0) = k3_yellow_0(A_95)
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_154,plain,(
    ! [A_69] : k1_yellow_0(k2_yellow_1(A_69),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_69)) ),
    inference(resolution,[status(thm)],[c_70,c_150])).

tff(c_10125,plain,(
    ! [A_986,B_987,D_988] :
      ( r1_orders_2(A_986,k1_yellow_0(A_986,B_987),D_988)
      | ~ r2_lattice3(A_986,B_987,D_988)
      | ~ m1_subset_1(D_988,u1_struct_0(A_986))
      | ~ r1_yellow_0(A_986,B_987)
      | ~ m1_subset_1(k1_yellow_0(A_986,B_987),u1_struct_0(A_986))
      | ~ l1_orders_2(A_986) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10129,plain,(
    ! [A_69,D_988] :
      ( r1_orders_2(k2_yellow_1(A_69),k1_yellow_0(k2_yellow_1(A_69),k1_xboole_0),D_988)
      | ~ r2_lattice3(k2_yellow_1(A_69),k1_xboole_0,D_988)
      | ~ m1_subset_1(D_988,u1_struct_0(k2_yellow_1(A_69)))
      | ~ r1_yellow_0(k2_yellow_1(A_69),k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(A_69)),u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_10125])).

tff(c_10134,plain,(
    ! [A_69,D_988] :
      ( r1_orders_2(k2_yellow_1(A_69),k3_yellow_0(k2_yellow_1(A_69)),D_988)
      | ~ r2_lattice3(k2_yellow_1(A_69),k1_xboole_0,D_988)
      | ~ m1_subset_1(D_988,A_69)
      | ~ r1_yellow_0(k2_yellow_1(A_69),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_149,c_80,c_80,c_154,c_10129])).

tff(c_11052,plain,(
    ! [A_1048,B_1049] :
      ( r3_orders_2(A_1048,B_1049,'#skF_5'(A_1048))
      | ~ r1_orders_2(A_1048,B_1049,'#skF_5'(A_1048))
      | ~ m1_subset_1(B_1049,u1_struct_0(A_1048))
      | ~ v3_orders_2(A_1048)
      | v2_struct_0(A_1048)
      | ~ v1_yellow_0(A_1048)
      | ~ l1_orders_2(A_1048) ) ),
    inference(resolution,[status(thm)],[c_48,c_1045])).

tff(c_11061,plain,(
    ! [B_1049] :
      ( r3_orders_2(k2_yellow_1('#skF_7'),B_1049,k1_xboole_0)
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1049,'#skF_5'(k2_yellow_1('#skF_7')))
      | ~ m1_subset_1(B_1049,u1_struct_0(k2_yellow_1('#skF_7')))
      | ~ v3_orders_2(k2_yellow_1('#skF_7'))
      | v2_struct_0(k2_yellow_1('#skF_7'))
      | ~ v1_yellow_0(k2_yellow_1('#skF_7'))
      | ~ l1_orders_2(k2_yellow_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10888,c_11052])).

tff(c_11067,plain,(
    ! [B_1049] :
      ( r3_orders_2(k2_yellow_1('#skF_7'),B_1049,k1_xboole_0)
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1049,k1_xboole_0)
      | ~ m1_subset_1(B_1049,'#skF_7')
      | v2_struct_0(k2_yellow_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9746,c_74,c_80,c_10888,c_11061])).

tff(c_11892,plain,(
    ! [B_1118] :
      ( r3_orders_2(k2_yellow_1('#skF_7'),B_1118,k1_xboole_0)
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1118,k1_xboole_0)
      | ~ m1_subset_1(B_1118,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9793,c_11067])).

tff(c_11897,plain,(
    ! [B_1118] :
      ( r1_tarski(B_1118,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1118,k1_xboole_0)
      | ~ m1_subset_1(B_1118,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11892,c_93])).

tff(c_11904,plain,(
    ! [B_1118] :
      ( r1_tarski(B_1118,k1_xboole_0)
      | v1_xboole_0('#skF_7')
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1118,k1_xboole_0)
      | ~ m1_subset_1(B_1118,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_11897])).

tff(c_11906,plain,(
    ! [B_1119] :
      ( r1_tarski(B_1119,k1_xboole_0)
      | ~ r1_orders_2(k2_yellow_1('#skF_7'),B_1119,k1_xboole_0)
      | ~ m1_subset_1(B_1119,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_11904])).

tff(c_11933,plain,
    ( r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')),k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1('#skF_7')),'#skF_7')
    | ~ r2_lattice3(k2_yellow_1('#skF_7'),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,'#skF_7')
    | ~ r1_yellow_0(k2_yellow_1('#skF_7'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10134,c_11906])).

tff(c_11968,plain,
    ( r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')),k1_xboole_0)
    | ~ r1_yellow_0(k2_yellow_1('#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_11609,c_149,c_11933])).

tff(c_11979,plain,(
    ~ r1_yellow_0(k2_yellow_1('#skF_7'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11968])).

tff(c_11982,plain,
    ( ~ l1_orders_2(k2_yellow_1('#skF_7'))
    | ~ v1_yellow_0(k2_yellow_1('#skF_7'))
    | ~ v5_orders_2(k2_yellow_1('#skF_7'))
    | v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_11979])).

tff(c_11985,plain,(
    v2_struct_0(k2_yellow_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9746,c_70,c_11982])).

tff(c_11987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9793,c_11985])).

tff(c_11988,plain,(
    r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11968])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_289,plain,(
    ! [A_131,B_132,B_133] :
      ( r2_hidden('#skF_2'(A_131,B_132),B_133)
      | ~ r1_tarski(A_131,B_133)
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_10,c_199])).

tff(c_305,plain,(
    ! [B_133,A_131,B_132] :
      ( ~ v1_xboole_0(B_133)
      | ~ r1_tarski(A_131,B_133)
      | r1_tarski(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_9803,plain,(
    ! [B_132] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),B_132) ) ),
    inference(resolution,[status(thm)],[c_9792,c_305])).

tff(c_9826,plain,(
    ! [B_966] : r1_tarski('#skF_5'(k2_yellow_1('#skF_7')),B_966) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9803])).

tff(c_267,plain,(
    ! [A_121,B_6,B_122] :
      ( r2_hidden('#skF_1'(A_121),B_6)
      | ~ r1_tarski(B_122,B_6)
      | ~ r1_tarski(A_121,B_122)
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_258,c_6])).

tff(c_9845,plain,(
    ! [A_121,B_966] :
      ( r2_hidden('#skF_1'(A_121),B_966)
      | ~ r1_tarski(A_121,'#skF_5'(k2_yellow_1('#skF_7')))
      | v1_xboole_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_9826,c_267])).

tff(c_11121,plain,(
    ! [A_1052,B_1053] :
      ( r2_hidden('#skF_1'(A_1052),B_1053)
      | ~ r1_tarski(A_1052,k1_xboole_0)
      | v1_xboole_0(A_1052) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10888,c_9845])).

tff(c_11138,plain,(
    ! [B_1053,A_1052] :
      ( ~ v1_xboole_0(B_1053)
      | ~ r1_tarski(A_1052,k1_xboole_0)
      | v1_xboole_0(A_1052) ) ),
    inference(resolution,[status(thm)],[c_11121,c_2])).

tff(c_11160,plain,(
    ! [B_1053] : ~ v1_xboole_0(B_1053) ),
    inference(splitLeft,[status(thm)],[c_11138])).

tff(c_11196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11160,c_12])).

tff(c_11197,plain,(
    ! [A_1052] :
      ( ~ r1_tarski(A_1052,k1_xboole_0)
      | v1_xboole_0(A_1052) ) ),
    inference(splitRight,[status(thm)],[c_11138])).

tff(c_12016,plain,(
    v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_11988,c_11197])).

tff(c_12040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10904,c_12016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.63/3.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.63/3.87  
% 10.63/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.63/3.87  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2
% 10.63/3.87  
% 10.63/3.87  %Foreground sorts:
% 10.63/3.87  
% 10.63/3.87  
% 10.63/3.87  %Background operators:
% 10.63/3.87  
% 10.63/3.87  
% 10.63/3.87  %Foreground operators:
% 10.63/3.87  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 10.63/3.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.63/3.87  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.63/3.87  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 10.63/3.87  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 10.63/3.87  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.63/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.63/3.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.63/3.87  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 10.63/3.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.63/3.87  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.63/3.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.63/3.87  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 10.63/3.87  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 10.63/3.87  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 10.63/3.87  tff('#skF_7', type, '#skF_7': $i).
% 10.63/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.63/3.87  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 10.63/3.87  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 10.63/3.87  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 10.63/3.87  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.63/3.87  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 10.63/3.87  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.63/3.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.63/3.87  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.63/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.63/3.87  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 10.63/3.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.63/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.63/3.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.63/3.87  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 10.63/3.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.63/3.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.63/3.87  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 10.63/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.63/3.87  
% 10.87/3.91  tff(f_201, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 10.87/3.91  tff(f_168, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 10.87/3.91  tff(f_180, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 10.87/3.91  tff(f_151, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 10.87/3.91  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 10.87/3.91  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.87/3.91  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 10.87/3.91  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.87/3.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.87/3.91  tff(f_176, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 10.87/3.91  tff(f_193, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 10.87/3.91  tff(f_68, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 10.87/3.91  tff(f_84, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 10.87/3.91  tff(f_49, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 10.87/3.91  tff(f_125, axiom, (![A]: (l1_orders_2(A) => (v1_yellow_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & r1_lattice3(A, u1_struct_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_yellow_0)).
% 10.87/3.91  tff(f_98, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 10.87/3.91  tff(f_164, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 10.87/3.91  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 10.87/3.91  tff(f_116, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 10.87/3.91  tff(f_143, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 10.87/3.91  tff(c_88, plain, (k3_yellow_0(k2_yellow_1('#skF_7'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_201])).
% 10.87/3.91  tff(c_70, plain, (![A_69]: (l1_orders_2(k2_yellow_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.87/3.91  tff(c_80, plain, (![A_71]: (u1_struct_0(k2_yellow_1(A_71))=A_71)), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.87/3.91  tff(c_144, plain, (![A_94]: (m1_subset_1(k3_yellow_0(A_94), u1_struct_0(A_94)) | ~l1_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.87/3.91  tff(c_147, plain, (![A_71]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_71)), A_71) | ~l1_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_144])).
% 10.87/3.91  tff(c_149, plain, (![A_71]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_71)), A_71))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_147])).
% 10.87/3.91  tff(c_92, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 10.87/3.91  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.87/3.91  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.87/3.91  tff(c_90, plain, (r2_hidden(k1_xboole_0, '#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 10.87/3.91  tff(c_130, plain, (![A_90, B_91]: (m1_subset_1(A_90, B_91) | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.87/3.91  tff(c_138, plain, (m1_subset_1(k1_xboole_0, '#skF_7')), inference(resolution, [status(thm)], [c_90, c_130])).
% 10.87/3.91  tff(c_165, plain, (![A_98, B_99]: (r2_hidden('#skF_2'(A_98, B_99), A_98) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.87/3.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.87/3.91  tff(c_173, plain, (![A_98, B_99]: (~v1_xboole_0(A_98) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_165, c_2])).
% 10.87/3.91  tff(c_74, plain, (![A_70]: (v3_orders_2(k2_yellow_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.87/3.91  tff(c_84, plain, (![A_72, B_76, C_78]: (r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~r1_tarski(B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(k2_yellow_1(A_72))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_72))) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.87/3.91  tff(c_94, plain, (![A_72, B_76, C_78]: (r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~r1_tarski(B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_84])).
% 10.87/3.91  tff(c_1203, plain, (![A_334, B_335, C_336]: (r1_orders_2(A_334, B_335, C_336) | ~r3_orders_2(A_334, B_335, C_336) | ~m1_subset_1(C_336, u1_struct_0(A_334)) | ~m1_subset_1(B_335, u1_struct_0(A_334)) | ~l1_orders_2(A_334) | ~v3_orders_2(A_334) | v2_struct_0(A_334))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.87/3.91  tff(c_1207, plain, (![A_72, B_76, C_78]: (r1_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(k2_yellow_1(A_72))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_72))) | ~l1_orders_2(k2_yellow_1(A_72)) | ~v3_orders_2(k2_yellow_1(A_72)) | v2_struct_0(k2_yellow_1(A_72)) | ~r1_tarski(B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_94, c_1203])).
% 10.87/3.91  tff(c_1213, plain, (![A_72, B_76, C_78]: (r1_orders_2(k2_yellow_1(A_72), B_76, C_78) | v2_struct_0(k2_yellow_1(A_72)) | ~r1_tarski(B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_80, c_80, c_1207])).
% 10.87/3.91  tff(c_78, plain, (![A_70]: (v5_orders_2(k2_yellow_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.87/3.91  tff(c_1214, plain, (![A_337, B_338, C_339]: (r1_orders_2(k2_yellow_1(A_337), B_338, C_339) | v2_struct_0(k2_yellow_1(A_337)) | ~r1_tarski(B_338, C_339) | ~m1_subset_1(C_339, A_337) | ~m1_subset_1(B_338, A_337) | v1_xboole_0(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_80, c_80, c_1207])).
% 10.87/3.91  tff(c_24, plain, (![C_23, B_21, A_17]: (C_23=B_21 | ~r1_orders_2(A_17, C_23, B_21) | ~r1_orders_2(A_17, B_21, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_17)) | ~m1_subset_1(B_21, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v5_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.87/3.91  tff(c_1220, plain, (![C_339, B_338, A_337]: (C_339=B_338 | ~r1_orders_2(k2_yellow_1(A_337), C_339, B_338) | ~m1_subset_1(B_338, u1_struct_0(k2_yellow_1(A_337))) | ~m1_subset_1(C_339, u1_struct_0(k2_yellow_1(A_337))) | ~l1_orders_2(k2_yellow_1(A_337)) | ~v5_orders_2(k2_yellow_1(A_337)) | v2_struct_0(k2_yellow_1(A_337)) | ~r1_tarski(B_338, C_339) | ~m1_subset_1(C_339, A_337) | ~m1_subset_1(B_338, A_337) | v1_xboole_0(A_337))), inference(resolution, [status(thm)], [c_1214, c_24])).
% 10.87/3.91  tff(c_1849, plain, (![C_398, B_399, A_400]: (C_398=B_399 | ~r1_orders_2(k2_yellow_1(A_400), C_398, B_399) | v2_struct_0(k2_yellow_1(A_400)) | ~r1_tarski(B_399, C_398) | ~m1_subset_1(C_398, A_400) | ~m1_subset_1(B_399, A_400) | v1_xboole_0(A_400))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_70, c_80, c_80, c_1220])).
% 10.87/3.91  tff(c_2001, plain, (![C_403, B_404, A_405]: (C_403=B_404 | ~r1_tarski(C_403, B_404) | v2_struct_0(k2_yellow_1(A_405)) | ~r1_tarski(B_404, C_403) | ~m1_subset_1(C_403, A_405) | ~m1_subset_1(B_404, A_405) | v1_xboole_0(A_405))), inference(resolution, [status(thm)], [c_1213, c_1849])).
% 10.87/3.91  tff(c_2014, plain, (![B_406, A_407, A_408]: (B_406=A_407 | v2_struct_0(k2_yellow_1(A_408)) | ~r1_tarski(B_406, A_407) | ~m1_subset_1(A_407, A_408) | ~m1_subset_1(B_406, A_408) | v1_xboole_0(A_408) | ~v1_xboole_0(A_407))), inference(resolution, [status(thm)], [c_173, c_2001])).
% 10.87/3.91  tff(c_2025, plain, (![B_409, A_410, A_411]: (B_409=A_410 | v2_struct_0(k2_yellow_1(A_411)) | ~m1_subset_1(B_409, A_411) | ~m1_subset_1(A_410, A_411) | v1_xboole_0(A_411) | ~v1_xboole_0(B_409) | ~v1_xboole_0(A_410))), inference(resolution, [status(thm)], [c_173, c_2014])).
% 10.87/3.91  tff(c_2065, plain, (![A_410]: (k1_xboole_0=A_410 | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(A_410, '#skF_7') | v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_410))), inference(resolution, [status(thm)], [c_138, c_2025])).
% 10.87/3.91  tff(c_2087, plain, (![A_410]: (k1_xboole_0=A_410 | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(A_410, '#skF_7') | v1_xboole_0('#skF_7') | ~v1_xboole_0(A_410))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2065])).
% 10.87/3.91  tff(c_2088, plain, (![A_410]: (k1_xboole_0=A_410 | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(A_410, '#skF_7') | ~v1_xboole_0(A_410))), inference(negUnitSimplification, [status(thm)], [c_92, c_2087])).
% 10.87/3.91  tff(c_2089, plain, (v2_struct_0(k2_yellow_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_2088])).
% 10.87/3.91  tff(c_139, plain, (![A_92]: (v1_xboole_0(u1_struct_0(A_92)) | ~l1_struct_0(A_92) | ~v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.87/3.91  tff(c_142, plain, (![A_71]: (v1_xboole_0(A_71) | ~l1_struct_0(k2_yellow_1(A_71)) | ~v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_139])).
% 10.87/3.91  tff(c_2095, plain, (v1_xboole_0('#skF_7') | ~l1_struct_0(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_2089, c_142])).
% 10.87/3.91  tff(c_2102, plain, (~l1_struct_0(k2_yellow_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_2095])).
% 10.87/3.91  tff(c_2117, plain, (~l1_orders_2(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_2102])).
% 10.87/3.91  tff(c_2121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2117])).
% 10.87/3.91  tff(c_2123, plain, (~v2_struct_0(k2_yellow_1('#skF_7'))), inference(splitRight, [status(thm)], [c_2088])).
% 10.87/3.91  tff(c_251, plain, (![A_119]: (r1_lattice3(A_119, u1_struct_0(A_119), '#skF_5'(A_119)) | ~v1_yellow_0(A_119) | ~l1_orders_2(A_119))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/3.91  tff(c_254, plain, (![A_71]: (r1_lattice3(k2_yellow_1(A_71), A_71, '#skF_5'(k2_yellow_1(A_71))) | ~v1_yellow_0(k2_yellow_1(A_71)) | ~l1_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_251])).
% 10.87/3.91  tff(c_256, plain, (![A_71]: (r1_lattice3(k2_yellow_1(A_71), A_71, '#skF_5'(k2_yellow_1(A_71))) | ~v1_yellow_0(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_254])).
% 10.87/3.91  tff(c_720, plain, (![A_237, C_238, D_239, B_240]: (r1_orders_2(A_237, C_238, D_239) | ~r2_hidden(D_239, B_240) | ~m1_subset_1(D_239, u1_struct_0(A_237)) | ~r1_lattice3(A_237, B_240, C_238) | ~m1_subset_1(C_238, u1_struct_0(A_237)) | ~l1_orders_2(A_237))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.87/3.91  tff(c_900, plain, (![A_289, C_290]: (r1_orders_2(A_289, C_290, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_289)) | ~r1_lattice3(A_289, '#skF_7', C_290) | ~m1_subset_1(C_290, u1_struct_0(A_289)) | ~l1_orders_2(A_289))), inference(resolution, [status(thm)], [c_90, c_720])).
% 10.87/3.91  tff(c_902, plain, (![A_71, C_290]: (r1_orders_2(k2_yellow_1(A_71), C_290, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_71) | ~r1_lattice3(k2_yellow_1(A_71), '#skF_7', C_290) | ~m1_subset_1(C_290, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_900])).
% 10.87/3.91  tff(c_904, plain, (![A_71, C_290]: (r1_orders_2(k2_yellow_1(A_71), C_290, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_71) | ~r1_lattice3(k2_yellow_1(A_71), '#skF_7', C_290) | ~m1_subset_1(C_290, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80, c_902])).
% 10.87/3.91  tff(c_1045, plain, (![A_299, B_300, C_301]: (r3_orders_2(A_299, B_300, C_301) | ~r1_orders_2(A_299, B_300, C_301) | ~m1_subset_1(C_301, u1_struct_0(A_299)) | ~m1_subset_1(B_300, u1_struct_0(A_299)) | ~l1_orders_2(A_299) | ~v3_orders_2(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.87/3.91  tff(c_1090, plain, (![A_71, B_300, C_301]: (r3_orders_2(k2_yellow_1(A_71), B_300, C_301) | ~r1_orders_2(k2_yellow_1(A_71), B_300, C_301) | ~m1_subset_1(C_301, A_71) | ~m1_subset_1(B_300, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v3_orders_2(k2_yellow_1(A_71)) | v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1045])).
% 10.87/3.91  tff(c_1173, plain, (![A_323, B_324, C_325]: (r3_orders_2(k2_yellow_1(A_323), B_324, C_325) | ~r1_orders_2(k2_yellow_1(A_323), B_324, C_325) | ~m1_subset_1(C_325, A_323) | ~m1_subset_1(B_324, A_323) | v2_struct_0(k2_yellow_1(A_323)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_80, c_1090])).
% 10.87/3.91  tff(c_86, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(k2_yellow_1(A_72))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_72))) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_193])).
% 10.87/3.91  tff(c_93, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_86])).
% 10.87/3.91  tff(c_1312, plain, (![B_367, C_368, A_369]: (r1_tarski(B_367, C_368) | v1_xboole_0(A_369) | ~r1_orders_2(k2_yellow_1(A_369), B_367, C_368) | ~m1_subset_1(C_368, A_369) | ~m1_subset_1(B_367, A_369) | v2_struct_0(k2_yellow_1(A_369)))), inference(resolution, [status(thm)], [c_1173, c_93])).
% 10.87/3.91  tff(c_1518, plain, (![C_379, A_380]: (r1_tarski(C_379, k1_xboole_0) | v1_xboole_0(A_380) | v2_struct_0(k2_yellow_1(A_380)) | ~m1_subset_1(k1_xboole_0, A_380) | ~r1_lattice3(k2_yellow_1(A_380), '#skF_7', C_379) | ~m1_subset_1(C_379, A_380))), inference(resolution, [status(thm)], [c_904, c_1312])).
% 10.87/3.91  tff(c_1594, plain, (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0) | v1_xboole_0('#skF_7') | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(k1_xboole_0, '#skF_7') | ~m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7') | ~v1_yellow_0(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_256, c_1518])).
% 10.87/3.91  tff(c_1643, plain, (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0) | v1_xboole_0('#skF_7') | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7') | ~v1_yellow_0(k2_yellow_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1594])).
% 10.87/3.91  tff(c_1644, plain, (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0) | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7') | ~v1_yellow_0(k2_yellow_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1643])).
% 10.87/3.91  tff(c_1660, plain, (~v1_yellow_0(k2_yellow_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1644])).
% 10.87/3.91  tff(c_418, plain, (![A_173, B_174, C_175]: (r2_hidden('#skF_3'(A_173, B_174, C_175), B_174) | r1_lattice3(A_173, B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.87/3.91  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.87/3.91  tff(c_428, plain, (![A_173, B_174, C_175]: (m1_subset_1('#skF_3'(A_173, B_174, C_175), B_174) | r1_lattice3(A_173, B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(resolution, [status(thm)], [c_418, c_14])).
% 10.87/3.91  tff(c_28, plain, (![A_24, C_32, B_31]: (~r1_orders_2(A_24, C_32, '#skF_3'(A_24, B_31, C_32)) | r1_lattice3(A_24, B_31, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.87/3.91  tff(c_1228, plain, (![A_337, B_31, B_338]: (r1_lattice3(k2_yellow_1(A_337), B_31, B_338) | ~m1_subset_1(B_338, u1_struct_0(k2_yellow_1(A_337))) | ~l1_orders_2(k2_yellow_1(A_337)) | v2_struct_0(k2_yellow_1(A_337)) | ~r1_tarski(B_338, '#skF_3'(k2_yellow_1(A_337), B_31, B_338)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_337), B_31, B_338), A_337) | ~m1_subset_1(B_338, A_337) | v1_xboole_0(A_337))), inference(resolution, [status(thm)], [c_1214, c_28])).
% 10.87/3.91  tff(c_9536, plain, (![A_953, B_954, B_955]: (r1_lattice3(k2_yellow_1(A_953), B_954, B_955) | v2_struct_0(k2_yellow_1(A_953)) | ~r1_tarski(B_955, '#skF_3'(k2_yellow_1(A_953), B_954, B_955)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_953), B_954, B_955), A_953) | ~m1_subset_1(B_955, A_953) | v1_xboole_0(A_953))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80, c_1228])).
% 10.87/3.91  tff(c_9557, plain, (![A_956, B_957, A_958]: (r1_lattice3(k2_yellow_1(A_956), B_957, A_958) | v2_struct_0(k2_yellow_1(A_956)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_956), B_957, A_958), A_956) | ~m1_subset_1(A_958, A_956) | v1_xboole_0(A_956) | ~v1_xboole_0(A_958))), inference(resolution, [status(thm)], [c_173, c_9536])).
% 10.87/3.91  tff(c_9565, plain, (![B_174, C_175]: (v2_struct_0(k2_yellow_1(B_174)) | ~m1_subset_1(C_175, B_174) | v1_xboole_0(B_174) | ~v1_xboole_0(C_175) | r1_lattice3(k2_yellow_1(B_174), B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(k2_yellow_1(B_174))) | ~l1_orders_2(k2_yellow_1(B_174)))), inference(resolution, [status(thm)], [c_428, c_9557])).
% 10.87/3.91  tff(c_9576, plain, (![B_959, C_960]: (v2_struct_0(k2_yellow_1(B_959)) | v1_xboole_0(B_959) | ~v1_xboole_0(C_960) | r1_lattice3(k2_yellow_1(B_959), B_959, C_960) | ~m1_subset_1(C_960, B_959))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80, c_9565])).
% 10.87/3.91  tff(c_328, plain, (![A_145, B_146]: (v1_yellow_0(A_145) | ~r1_lattice3(A_145, u1_struct_0(A_145), B_146) | ~m1_subset_1(B_146, u1_struct_0(A_145)) | ~l1_orders_2(A_145))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/3.91  tff(c_334, plain, (![A_71, B_146]: (v1_yellow_0(k2_yellow_1(A_71)) | ~r1_lattice3(k2_yellow_1(A_71), A_71, B_146) | ~m1_subset_1(B_146, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_328])).
% 10.87/3.91  tff(c_337, plain, (![A_71, B_146]: (v1_yellow_0(k2_yellow_1(A_71)) | ~r1_lattice3(k2_yellow_1(A_71), A_71, B_146) | ~m1_subset_1(B_146, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80, c_334])).
% 10.87/3.91  tff(c_9657, plain, (![B_961, C_962]: (v1_yellow_0(k2_yellow_1(B_961)) | v2_struct_0(k2_yellow_1(B_961)) | v1_xboole_0(B_961) | ~v1_xboole_0(C_962) | ~m1_subset_1(C_962, B_961))), inference(resolution, [status(thm)], [c_9576, c_337])).
% 10.87/3.91  tff(c_9707, plain, (v1_yellow_0(k2_yellow_1('#skF_7')) | v2_struct_0(k2_yellow_1('#skF_7')) | v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_138, c_9657])).
% 10.87/3.91  tff(c_9742, plain, (v1_yellow_0(k2_yellow_1('#skF_7')) | v2_struct_0(k2_yellow_1('#skF_7')) | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9707])).
% 10.87/3.91  tff(c_9744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_2123, c_1660, c_9742])).
% 10.87/3.91  tff(c_9746, plain, (v1_yellow_0(k2_yellow_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1644])).
% 10.87/3.91  tff(c_245, plain, (![A_118]: (m1_subset_1('#skF_5'(A_118), u1_struct_0(A_118)) | ~v1_yellow_0(A_118) | ~l1_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/3.91  tff(c_248, plain, (![A_71]: (m1_subset_1('#skF_5'(k2_yellow_1(A_71)), A_71) | ~v1_yellow_0(k2_yellow_1(A_71)) | ~l1_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_245])).
% 10.87/3.91  tff(c_250, plain, (![A_71]: (m1_subset_1('#skF_5'(k2_yellow_1(A_71)), A_71) | ~v1_yellow_0(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_248])).
% 10.87/3.91  tff(c_9745, plain, (~m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7') | v2_struct_0(k2_yellow_1('#skF_7')) | r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1644])).
% 10.87/3.91  tff(c_9747, plain, (~m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7')), inference(splitLeft, [status(thm)], [c_9745])).
% 10.87/3.91  tff(c_9750, plain, (~v1_yellow_0(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_250, c_9747])).
% 10.87/3.91  tff(c_9754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9746, c_9750])).
% 10.87/3.91  tff(c_9755, plain, (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0) | v2_struct_0(k2_yellow_1('#skF_7'))), inference(splitRight, [status(thm)], [c_9745])).
% 10.87/3.91  tff(c_9757, plain, (v2_struct_0(k2_yellow_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_9755])).
% 10.87/3.91  tff(c_9763, plain, (v1_xboole_0('#skF_7') | ~l1_struct_0(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_9757, c_142])).
% 10.87/3.91  tff(c_9769, plain, (~l1_struct_0(k2_yellow_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_9763])).
% 10.87/3.91  tff(c_9787, plain, (~l1_orders_2(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_18, c_9769])).
% 10.87/3.91  tff(c_9791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_9787])).
% 10.87/3.91  tff(c_9793, plain, (~v2_struct_0(k2_yellow_1('#skF_7'))), inference(splitRight, [status(thm)], [c_9755])).
% 10.87/3.91  tff(c_10637, plain, (![C_1031, B_1032, A_1033]: (C_1031=B_1032 | ~r1_orders_2(k2_yellow_1(A_1033), C_1031, B_1032) | v2_struct_0(k2_yellow_1(A_1033)) | ~r1_tarski(B_1032, C_1031) | ~m1_subset_1(C_1031, A_1033) | ~m1_subset_1(B_1032, A_1033) | v1_xboole_0(A_1033))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_70, c_80, c_80, c_1220])).
% 10.87/3.91  tff(c_10711, plain, (![C_1034, B_1035, A_1036]: (C_1034=B_1035 | ~r1_tarski(C_1034, B_1035) | v2_struct_0(k2_yellow_1(A_1036)) | ~r1_tarski(B_1035, C_1034) | ~m1_subset_1(C_1034, A_1036) | ~m1_subset_1(B_1035, A_1036) | v1_xboole_0(A_1036))), inference(resolution, [status(thm)], [c_1213, c_10637])).
% 10.87/3.91  tff(c_10727, plain, (![B_1037, A_1038, A_1039]: (B_1037=A_1038 | v2_struct_0(k2_yellow_1(A_1039)) | ~r1_tarski(B_1037, A_1038) | ~m1_subset_1(A_1038, A_1039) | ~m1_subset_1(B_1037, A_1039) | v1_xboole_0(A_1039) | ~v1_xboole_0(A_1038))), inference(resolution, [status(thm)], [c_173, c_10711])).
% 10.87/3.91  tff(c_10741, plain, (![B_1040, A_1041, A_1042]: (B_1040=A_1041 | v2_struct_0(k2_yellow_1(A_1042)) | ~m1_subset_1(B_1040, A_1042) | ~m1_subset_1(A_1041, A_1042) | v1_xboole_0(A_1042) | ~v1_xboole_0(B_1040) | ~v1_xboole_0(A_1041))), inference(resolution, [status(thm)], [c_173, c_10727])).
% 10.87/3.91  tff(c_10783, plain, (![A_1041]: (k1_xboole_0=A_1041 | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(A_1041, '#skF_7') | v1_xboole_0('#skF_7') | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_1041))), inference(resolution, [status(thm)], [c_138, c_10741])).
% 10.87/3.91  tff(c_10809, plain, (![A_1041]: (k1_xboole_0=A_1041 | v2_struct_0(k2_yellow_1('#skF_7')) | ~m1_subset_1(A_1041, '#skF_7') | v1_xboole_0('#skF_7') | ~v1_xboole_0(A_1041))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10783])).
% 10.87/3.91  tff(c_10827, plain, (![A_1046]: (k1_xboole_0=A_1046 | ~m1_subset_1(A_1046, '#skF_7') | ~v1_xboole_0(A_1046))), inference(negUnitSimplification, [status(thm)], [c_92, c_9793, c_10809])).
% 10.87/3.91  tff(c_10878, plain, (k3_yellow_0(k2_yellow_1('#skF_7'))=k1_xboole_0 | ~v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7')))), inference(resolution, [status(thm)], [c_149, c_10827])).
% 10.87/3.91  tff(c_10904, plain, (~v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_88, c_10878])).
% 10.87/3.91  tff(c_66, plain, (![A_68]: (r1_yellow_0(A_68, k1_xboole_0) | ~l1_orders_2(A_68) | ~v1_yellow_0(A_68) | ~v5_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.87/3.91  tff(c_9792, plain, (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_9755])).
% 10.87/3.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.87/3.91  tff(c_199, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.87/3.91  tff(c_258, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121), B_122) | ~r1_tarski(A_121, B_122) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_4, c_199])).
% 10.87/3.91  tff(c_269, plain, (![B_122, A_121]: (~v1_xboole_0(B_122) | ~r1_tarski(A_121, B_122) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_258, c_2])).
% 10.87/3.91  tff(c_9808, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7')))), inference(resolution, [status(thm)], [c_9792, c_269])).
% 10.87/3.91  tff(c_9823, plain, (v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9808])).
% 10.87/3.91  tff(c_9756, plain, (m1_subset_1('#skF_5'(k2_yellow_1('#skF_7')), '#skF_7')), inference(splitRight, [status(thm)], [c_9745])).
% 10.87/3.91  tff(c_10830, plain, ('#skF_5'(k2_yellow_1('#skF_7'))=k1_xboole_0 | ~v1_xboole_0('#skF_5'(k2_yellow_1('#skF_7')))), inference(resolution, [status(thm)], [c_9756, c_10827])).
% 10.87/3.91  tff(c_10888, plain, ('#skF_5'(k2_yellow_1('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9823, c_10830])).
% 10.87/3.91  tff(c_48, plain, (![A_49]: (m1_subset_1('#skF_5'(A_49), u1_struct_0(A_49)) | ~v1_yellow_0(A_49) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.87/3.91  tff(c_351, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_4'(A_156, B_157, C_158), B_157) | r2_lattice3(A_156, B_157, C_158) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~l1_orders_2(A_156))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.87/3.91  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.87/3.91  tff(c_1178, plain, (![A_326, B_327, C_328, B_329]: (r2_hidden('#skF_4'(A_326, B_327, C_328), B_329) | ~r1_tarski(B_327, B_329) | r2_lattice3(A_326, B_327, C_328) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(resolution, [status(thm)], [c_351, c_6])).
% 10.87/3.91  tff(c_1195, plain, (![B_329, B_327, A_326, C_328]: (~v1_xboole_0(B_329) | ~r1_tarski(B_327, B_329) | r2_lattice3(A_326, B_327, C_328) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(resolution, [status(thm)], [c_1178, c_2])).
% 10.87/3.91  tff(c_9795, plain, (![A_326, C_328]: (~v1_xboole_0(k1_xboole_0) | r2_lattice3(A_326, '#skF_5'(k2_yellow_1('#skF_7')), C_328) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(resolution, [status(thm)], [c_9792, c_1195])).
% 10.87/3.91  tff(c_9811, plain, (![A_326, C_328]: (r2_lattice3(A_326, '#skF_5'(k2_yellow_1('#skF_7')), C_328) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9795])).
% 10.87/3.91  tff(c_11436, plain, (![A_1074, C_1075]: (r2_lattice3(A_1074, k1_xboole_0, C_1075) | ~m1_subset_1(C_1075, u1_struct_0(A_1074)) | ~l1_orders_2(A_1074))), inference(demodulation, [status(thm), theory('equality')], [c_10888, c_9811])).
% 10.87/3.91  tff(c_11597, plain, (![A_1088]: (r2_lattice3(A_1088, k1_xboole_0, '#skF_5'(A_1088)) | ~v1_yellow_0(A_1088) | ~l1_orders_2(A_1088))), inference(resolution, [status(thm)], [c_48, c_11436])).
% 10.87/3.91  tff(c_11604, plain, (r2_lattice3(k2_yellow_1('#skF_7'), k1_xboole_0, k1_xboole_0) | ~v1_yellow_0(k2_yellow_1('#skF_7')) | ~l1_orders_2(k2_yellow_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10888, c_11597])).
% 10.87/3.91  tff(c_11609, plain, (r2_lattice3(k2_yellow_1('#skF_7'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9746, c_11604])).
% 10.87/3.91  tff(c_150, plain, (![A_95]: (k1_yellow_0(A_95, k1_xboole_0)=k3_yellow_0(A_95) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.87/3.91  tff(c_154, plain, (![A_69]: (k1_yellow_0(k2_yellow_1(A_69), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_69)))), inference(resolution, [status(thm)], [c_70, c_150])).
% 10.87/3.91  tff(c_10125, plain, (![A_986, B_987, D_988]: (r1_orders_2(A_986, k1_yellow_0(A_986, B_987), D_988) | ~r2_lattice3(A_986, B_987, D_988) | ~m1_subset_1(D_988, u1_struct_0(A_986)) | ~r1_yellow_0(A_986, B_987) | ~m1_subset_1(k1_yellow_0(A_986, B_987), u1_struct_0(A_986)) | ~l1_orders_2(A_986))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.87/3.91  tff(c_10129, plain, (![A_69, D_988]: (r1_orders_2(k2_yellow_1(A_69), k1_yellow_0(k2_yellow_1(A_69), k1_xboole_0), D_988) | ~r2_lattice3(k2_yellow_1(A_69), k1_xboole_0, D_988) | ~m1_subset_1(D_988, u1_struct_0(k2_yellow_1(A_69))) | ~r1_yellow_0(k2_yellow_1(A_69), k1_xboole_0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(A_69)), u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_10125])).
% 10.87/3.91  tff(c_10134, plain, (![A_69, D_988]: (r1_orders_2(k2_yellow_1(A_69), k3_yellow_0(k2_yellow_1(A_69)), D_988) | ~r2_lattice3(k2_yellow_1(A_69), k1_xboole_0, D_988) | ~m1_subset_1(D_988, A_69) | ~r1_yellow_0(k2_yellow_1(A_69), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_149, c_80, c_80, c_154, c_10129])).
% 10.87/3.91  tff(c_11052, plain, (![A_1048, B_1049]: (r3_orders_2(A_1048, B_1049, '#skF_5'(A_1048)) | ~r1_orders_2(A_1048, B_1049, '#skF_5'(A_1048)) | ~m1_subset_1(B_1049, u1_struct_0(A_1048)) | ~v3_orders_2(A_1048) | v2_struct_0(A_1048) | ~v1_yellow_0(A_1048) | ~l1_orders_2(A_1048))), inference(resolution, [status(thm)], [c_48, c_1045])).
% 10.87/3.91  tff(c_11061, plain, (![B_1049]: (r3_orders_2(k2_yellow_1('#skF_7'), B_1049, k1_xboole_0) | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1049, '#skF_5'(k2_yellow_1('#skF_7'))) | ~m1_subset_1(B_1049, u1_struct_0(k2_yellow_1('#skF_7'))) | ~v3_orders_2(k2_yellow_1('#skF_7')) | v2_struct_0(k2_yellow_1('#skF_7')) | ~v1_yellow_0(k2_yellow_1('#skF_7')) | ~l1_orders_2(k2_yellow_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_10888, c_11052])).
% 10.87/3.91  tff(c_11067, plain, (![B_1049]: (r3_orders_2(k2_yellow_1('#skF_7'), B_1049, k1_xboole_0) | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1049, k1_xboole_0) | ~m1_subset_1(B_1049, '#skF_7') | v2_struct_0(k2_yellow_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9746, c_74, c_80, c_10888, c_11061])).
% 10.87/3.91  tff(c_11892, plain, (![B_1118]: (r3_orders_2(k2_yellow_1('#skF_7'), B_1118, k1_xboole_0) | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1118, k1_xboole_0) | ~m1_subset_1(B_1118, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_9793, c_11067])).
% 10.87/3.91  tff(c_11897, plain, (![B_1118]: (r1_tarski(B_1118, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, '#skF_7') | v1_xboole_0('#skF_7') | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1118, k1_xboole_0) | ~m1_subset_1(B_1118, '#skF_7'))), inference(resolution, [status(thm)], [c_11892, c_93])).
% 10.87/3.91  tff(c_11904, plain, (![B_1118]: (r1_tarski(B_1118, k1_xboole_0) | v1_xboole_0('#skF_7') | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1118, k1_xboole_0) | ~m1_subset_1(B_1118, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_11897])).
% 10.87/3.91  tff(c_11906, plain, (![B_1119]: (r1_tarski(B_1119, k1_xboole_0) | ~r1_orders_2(k2_yellow_1('#skF_7'), B_1119, k1_xboole_0) | ~m1_subset_1(B_1119, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_92, c_11904])).
% 10.87/3.91  tff(c_11933, plain, (r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')), k1_xboole_0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1('#skF_7')), '#skF_7') | ~r2_lattice3(k2_yellow_1('#skF_7'), k1_xboole_0, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, '#skF_7') | ~r1_yellow_0(k2_yellow_1('#skF_7'), k1_xboole_0)), inference(resolution, [status(thm)], [c_10134, c_11906])).
% 10.87/3.91  tff(c_11968, plain, (r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')), k1_xboole_0) | ~r1_yellow_0(k2_yellow_1('#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_11609, c_149, c_11933])).
% 10.87/3.91  tff(c_11979, plain, (~r1_yellow_0(k2_yellow_1('#skF_7'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11968])).
% 10.87/3.91  tff(c_11982, plain, (~l1_orders_2(k2_yellow_1('#skF_7')) | ~v1_yellow_0(k2_yellow_1('#skF_7')) | ~v5_orders_2(k2_yellow_1('#skF_7')) | v2_struct_0(k2_yellow_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_11979])).
% 10.87/3.91  tff(c_11985, plain, (v2_struct_0(k2_yellow_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9746, c_70, c_11982])).
% 10.87/3.91  tff(c_11987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9793, c_11985])).
% 10.87/3.91  tff(c_11988, plain, (r1_tarski(k3_yellow_0(k2_yellow_1('#skF_7')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_11968])).
% 10.87/3.91  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.87/3.91  tff(c_289, plain, (![A_131, B_132, B_133]: (r2_hidden('#skF_2'(A_131, B_132), B_133) | ~r1_tarski(A_131, B_133) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_10, c_199])).
% 10.87/3.91  tff(c_305, plain, (![B_133, A_131, B_132]: (~v1_xboole_0(B_133) | ~r1_tarski(A_131, B_133) | r1_tarski(A_131, B_132))), inference(resolution, [status(thm)], [c_289, c_2])).
% 10.87/3.91  tff(c_9803, plain, (![B_132]: (~v1_xboole_0(k1_xboole_0) | r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), B_132))), inference(resolution, [status(thm)], [c_9792, c_305])).
% 10.87/3.91  tff(c_9826, plain, (![B_966]: (r1_tarski('#skF_5'(k2_yellow_1('#skF_7')), B_966))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9803])).
% 10.87/3.91  tff(c_267, plain, (![A_121, B_6, B_122]: (r2_hidden('#skF_1'(A_121), B_6) | ~r1_tarski(B_122, B_6) | ~r1_tarski(A_121, B_122) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_258, c_6])).
% 10.87/3.91  tff(c_9845, plain, (![A_121, B_966]: (r2_hidden('#skF_1'(A_121), B_966) | ~r1_tarski(A_121, '#skF_5'(k2_yellow_1('#skF_7'))) | v1_xboole_0(A_121))), inference(resolution, [status(thm)], [c_9826, c_267])).
% 10.87/3.91  tff(c_11121, plain, (![A_1052, B_1053]: (r2_hidden('#skF_1'(A_1052), B_1053) | ~r1_tarski(A_1052, k1_xboole_0) | v1_xboole_0(A_1052))), inference(demodulation, [status(thm), theory('equality')], [c_10888, c_9845])).
% 10.87/3.91  tff(c_11138, plain, (![B_1053, A_1052]: (~v1_xboole_0(B_1053) | ~r1_tarski(A_1052, k1_xboole_0) | v1_xboole_0(A_1052))), inference(resolution, [status(thm)], [c_11121, c_2])).
% 10.87/3.91  tff(c_11160, plain, (![B_1053]: (~v1_xboole_0(B_1053))), inference(splitLeft, [status(thm)], [c_11138])).
% 10.87/3.91  tff(c_11196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11160, c_12])).
% 10.87/3.91  tff(c_11197, plain, (![A_1052]: (~r1_tarski(A_1052, k1_xboole_0) | v1_xboole_0(A_1052))), inference(splitRight, [status(thm)], [c_11138])).
% 10.87/3.91  tff(c_12016, plain, (v1_xboole_0(k3_yellow_0(k2_yellow_1('#skF_7')))), inference(resolution, [status(thm)], [c_11988, c_11197])).
% 10.87/3.91  tff(c_12040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10904, c_12016])).
% 10.87/3.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.87/3.91  
% 10.87/3.91  Inference rules
% 10.87/3.91  ----------------------
% 10.87/3.91  #Ref     : 0
% 10.87/3.91  #Sup     : 2366
% 10.87/3.91  #Fact    : 0
% 10.87/3.91  #Define  : 0
% 10.87/3.91  #Split   : 16
% 10.87/3.91  #Chain   : 0
% 10.87/3.91  #Close   : 0
% 10.87/3.91  
% 10.87/3.91  Ordering : KBO
% 10.87/3.91  
% 10.87/3.91  Simplification rules
% 10.87/3.91  ----------------------
% 10.87/3.91  #Subsume      : 782
% 10.87/3.91  #Demod        : 2917
% 10.87/3.91  #Tautology    : 324
% 10.87/3.91  #SimpNegUnit  : 80
% 10.87/3.91  #BackRed      : 34
% 10.87/3.91  
% 10.87/3.91  #Partial instantiations: 0
% 10.87/3.91  #Strategies tried      : 1
% 10.87/3.91  
% 10.87/3.91  Timing (in seconds)
% 10.87/3.91  ----------------------
% 10.87/3.91  Preprocessing        : 0.37
% 10.87/3.91  Parsing              : 0.19
% 10.87/3.91  CNF conversion       : 0.03
% 10.87/3.91  Main loop            : 2.75
% 10.87/3.91  Inferencing          : 0.91
% 10.87/3.91  Reduction            : 0.80
% 10.87/3.91  Demodulation         : 0.53
% 10.87/3.91  BG Simplification    : 0.08
% 10.87/3.91  Subsumption          : 0.79
% 10.87/3.91  Abstraction          : 0.11
% 10.87/3.91  MUC search           : 0.00
% 10.87/3.91  Cooper               : 0.00
% 10.87/3.91  Total                : 3.19
% 10.87/3.91  Index Insertion      : 0.00
% 10.87/3.91  Index Deletion       : 0.00
% 10.87/3.91  Index Matching       : 0.00
% 10.87/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
