%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:13 EST 2020

% Result     : Theorem 36.61s
% Output     : CNFRefutation 36.61s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 185 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  147 ( 402 expanded)
%              Number of equality atoms :   35 ( 120 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_86,plain,(
    ! [A_30,B_31,C_32] :
      ( k8_relat_1(k3_xboole_0(A_30,B_31),C_32) = k8_relat_1(A_30,k8_relat_1(B_31,C_32))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    ! [B_2,C_32] :
      ( k8_relat_1(B_2,k8_relat_1(B_2,C_32)) = k8_relat_1(B_2,C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_86])).

tff(c_101,plain,(
    ! [A_30,B_31,C_32] :
      ( v1_relat_1(k8_relat_1(A_30,k8_relat_1(B_31,C_32)))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_12])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k8_relat_1(k3_xboole_0(A_11,B_12),C_13) = k8_relat_1(A_11,k8_relat_1(B_12,C_13))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k8_relat_1(A_9,B_10),B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_228,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(k8_relat_1(A_40,k8_relat_1(B_41,C_42)),C_42)
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_535,plain,(
    ! [A_53,A_54,B_55,C_56] :
      ( r1_tarski(k8_relat_1(A_53,k8_relat_1(A_54,k8_relat_1(B_55,C_56))),C_56)
      | ~ v1_relat_1(C_56)
      | ~ v1_relat_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_228])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2686,plain,(
    ! [A_122,A_123,B_124,C_125] :
      ( k3_xboole_0(k8_relat_1(A_122,k8_relat_1(A_123,k8_relat_1(B_124,C_125))),C_125) = k8_relat_1(A_122,k8_relat_1(A_123,k8_relat_1(B_124,C_125)))
      | ~ v1_relat_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_535,c_8])).

tff(c_5392,plain,(
    ! [A_152,B_153,C_154] :
      ( k8_relat_1(A_152,k8_relat_1(B_153,k8_relat_1(B_153,C_154))) = k3_xboole_0(k8_relat_1(A_152,k8_relat_1(B_153,C_154)),C_154)
      | ~ v1_relat_1(C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2686])).

tff(c_13893,plain,(
    ! [A_202,B_203,C_204] :
      ( v1_relat_1(k3_xboole_0(k8_relat_1(A_202,k8_relat_1(B_203,C_204)),C_204))
      | ~ v1_relat_1(k8_relat_1(B_203,k8_relat_1(B_203,C_204)))
      | ~ v1_relat_1(C_204)
      | ~ v1_relat_1(C_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5392,c_12])).

tff(c_14023,plain,(
    ! [A_205,B_206,C_207] :
      ( v1_relat_1(k3_xboole_0(k8_relat_1(A_205,k8_relat_1(B_206,C_207)),C_207))
      | ~ v1_relat_1(C_207) ) ),
    inference(resolution,[status(thm)],[c_101,c_13893])).

tff(c_14207,plain,(
    ! [B_2,C_32] :
      ( v1_relat_1(k3_xboole_0(k8_relat_1(B_2,C_32),C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_14023])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_110,plain,(
    ! [C_32] :
      ( k8_relat_1('#skF_1',k8_relat_1('#skF_2',C_32)) = k8_relat_1('#skF_1',C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_57,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(k8_relat_1(A_22,B_23),B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(k8_relat_1(A_22,B_23),B_23) = k8_relat_1(A_22,B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_57,c_8])).

tff(c_287,plain,(
    ! [A_47,B_48,C_49] :
      ( k3_xboole_0(k8_relat_1(A_47,k8_relat_1(B_48,C_49)),C_49) = k8_relat_1(A_47,k8_relat_1(B_48,C_49))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_228,c_8])).

tff(c_308,plain,(
    ! [B_2,C_32] :
      ( k8_relat_1(B_2,k8_relat_1(B_2,C_32)) = k3_xboole_0(k8_relat_1(B_2,C_32),C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_287])).

tff(c_24055,plain,(
    ! [A_294,B_295,C_296] :
      ( r1_tarski(k8_relat_1(A_294,k3_xboole_0(k8_relat_1(B_295,C_296),C_296)),C_296)
      | ~ v1_relat_1(C_296)
      | ~ v1_relat_1(C_296)
      | ~ v1_relat_1(C_296)
      | ~ v1_relat_1(C_296)
      | ~ v1_relat_1(C_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_535])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27758,plain,(
    ! [A_322,B_323,C_324] :
      ( k8_relat_1(A_322,k3_xboole_0(k8_relat_1(B_323,C_324),C_324)) = C_324
      | ~ r1_tarski(C_324,k8_relat_1(A_322,k3_xboole_0(k8_relat_1(B_323,C_324),C_324)))
      | ~ v1_relat_1(C_324) ) ),
    inference(resolution,[status(thm)],[c_24055,c_2])).

tff(c_32538,plain,(
    ! [A_358,A_359,B_360] :
      ( k8_relat_1(A_358,k3_xboole_0(k8_relat_1(A_359,B_360),B_360)) = B_360
      | ~ r1_tarski(B_360,k8_relat_1(A_358,k8_relat_1(A_359,B_360)))
      | ~ v1_relat_1(B_360)
      | ~ v1_relat_1(B_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_27758])).

tff(c_34464,plain,(
    ! [C_367] :
      ( k8_relat_1('#skF_1',k3_xboole_0(k8_relat_1('#skF_2',C_367),C_367)) = C_367
      | ~ r1_tarski(C_367,k8_relat_1('#skF_1',C_367))
      | ~ v1_relat_1(C_367)
      | ~ v1_relat_1(C_367)
      | ~ v1_relat_1(C_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_32538])).

tff(c_24210,plain,(
    ! [A_294,B_295,C_296] :
      ( k8_relat_1(A_294,k3_xboole_0(k8_relat_1(B_295,C_296),C_296)) = C_296
      | ~ r1_tarski(C_296,k8_relat_1(A_294,k3_xboole_0(k8_relat_1(B_295,C_296),C_296)))
      | ~ v1_relat_1(C_296) ) ),
    inference(resolution,[status(thm)],[c_24055,c_2])).

tff(c_34531,plain,(
    ! [C_367] :
      ( k8_relat_1('#skF_1',k3_xboole_0(k8_relat_1('#skF_2',C_367),C_367)) = C_367
      | ~ r1_tarski(C_367,C_367)
      | ~ v1_relat_1(C_367)
      | ~ r1_tarski(C_367,k8_relat_1('#skF_1',C_367))
      | ~ v1_relat_1(C_367)
      | ~ v1_relat_1(C_367)
      | ~ v1_relat_1(C_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34464,c_24210])).

tff(c_34989,plain,(
    ! [C_368] :
      ( k8_relat_1('#skF_1',k3_xboole_0(k8_relat_1('#skF_2',C_368),C_368)) = C_368
      | ~ r1_tarski(C_368,k8_relat_1('#skF_1',C_368))
      | ~ v1_relat_1(C_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34531])).

tff(c_111298,plain,(
    ! [C_618] :
      ( r1_tarski(C_618,k3_xboole_0(k8_relat_1('#skF_2',C_618),C_618))
      | ~ v1_relat_1(k3_xboole_0(k8_relat_1('#skF_2',C_618),C_618))
      | ~ r1_tarski(C_618,k8_relat_1('#skF_1',C_618))
      | ~ v1_relat_1(C_618) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34989,c_14])).

tff(c_62,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_9,B_10] :
      ( k8_relat_1(A_9,B_10) = B_10
      | ~ r1_tarski(B_10,k8_relat_1(A_9,B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_2057,plain,(
    ! [A_100,B_101,C_102] :
      ( k8_relat_1(k3_xboole_0(A_100,B_101),C_102) = C_102
      | ~ r1_tarski(C_102,k8_relat_1(A_100,k8_relat_1(B_101,C_102)))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_69])).

tff(c_2087,plain,(
    ! [B_2,C_32] :
      ( k8_relat_1(k3_xboole_0(B_2,B_2),C_32) = C_32
      | ~ r1_tarski(C_32,k3_xboole_0(k8_relat_1(B_2,C_32),C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_2057])).

tff(c_2118,plain,(
    ! [B_2,C_32] :
      ( k8_relat_1(B_2,C_32) = C_32
      | ~ r1_tarski(C_32,k3_xboole_0(k8_relat_1(B_2,C_32),C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_2087])).

tff(c_112692,plain,(
    ! [C_621] :
      ( k8_relat_1('#skF_2',C_621) = C_621
      | ~ v1_relat_1(k3_xboole_0(k8_relat_1('#skF_2',C_621),C_621))
      | ~ r1_tarski(C_621,k8_relat_1('#skF_1',C_621))
      | ~ v1_relat_1(C_621) ) ),
    inference(resolution,[status(thm)],[c_111298,c_2118])).

tff(c_112820,plain,(
    ! [C_622] :
      ( k8_relat_1('#skF_2',C_622) = C_622
      | ~ r1_tarski(C_622,k8_relat_1('#skF_1',C_622))
      | ~ v1_relat_1(C_622) ) ),
    inference(resolution,[status(thm)],[c_14207,c_112692])).

tff(c_113009,plain,(
    ! [C_32] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',C_32)) = k8_relat_1('#skF_1',C_32)
      | ~ r1_tarski(k8_relat_1('#skF_1',C_32),k8_relat_1('#skF_1',C_32))
      | ~ v1_relat_1(k8_relat_1('#skF_1',C_32))
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_112820])).

tff(c_113018,plain,(
    ! [C_623] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',C_623)) = k8_relat_1('#skF_1',C_623)
      | ~ v1_relat_1(k8_relat_1('#skF_1',C_623))
      | ~ v1_relat_1(C_623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_113009])).

tff(c_113308,plain,(
    ! [B_624] :
      ( k8_relat_1('#skF_2',k8_relat_1('#skF_1',B_624)) = k8_relat_1('#skF_1',B_624)
      | ~ v1_relat_1(B_624) ) ),
    inference(resolution,[status(thm)],[c_12,c_113018])).

tff(c_18,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114421,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_113308,c_18])).

tff(c_114739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_114421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.61/24.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.61/24.07  
% 36.61/24.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.61/24.07  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 36.61/24.07  
% 36.61/24.07  %Foreground sorts:
% 36.61/24.07  
% 36.61/24.07  
% 36.61/24.07  %Background operators:
% 36.61/24.07  
% 36.61/24.07  
% 36.61/24.07  %Foreground operators:
% 36.61/24.07  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 36.61/24.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.61/24.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.61/24.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.61/24.07  tff('#skF_2', type, '#skF_2': $i).
% 36.61/24.07  tff('#skF_3', type, '#skF_3': $i).
% 36.61/24.07  tff('#skF_1', type, '#skF_1': $i).
% 36.61/24.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.61/24.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.61/24.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.61/24.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.61/24.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 36.61/24.07  
% 36.61/24.08  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 36.61/24.08  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 36.61/24.08  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.61/24.08  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.61/24.08  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 36.61/24.08  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 36.61/24.08  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.61/24.08  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k8_relat_1(A_7, B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.61/24.08  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.61/24.08  tff(c_26, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.61/24.08  tff(c_33, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_26])).
% 36.61/24.08  tff(c_86, plain, (![A_30, B_31, C_32]: (k8_relat_1(k3_xboole_0(A_30, B_31), C_32)=k8_relat_1(A_30, k8_relat_1(B_31, C_32)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.61/24.08  tff(c_113, plain, (![B_2, C_32]: (k8_relat_1(B_2, k8_relat_1(B_2, C_32))=k8_relat_1(B_2, C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_33, c_86])).
% 36.61/24.08  tff(c_101, plain, (![A_30, B_31, C_32]: (v1_relat_1(k8_relat_1(A_30, k8_relat_1(B_31, C_32))) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_86, c_12])).
% 36.61/24.08  tff(c_16, plain, (![A_11, B_12, C_13]: (k8_relat_1(k3_xboole_0(A_11, B_12), C_13)=k8_relat_1(A_11, k8_relat_1(B_12, C_13)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.61/24.08  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k8_relat_1(A_9, B_10), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.61/24.08  tff(c_228, plain, (![A_40, B_41, C_42]: (r1_tarski(k8_relat_1(A_40, k8_relat_1(B_41, C_42)), C_42) | ~v1_relat_1(C_42) | ~v1_relat_1(C_42))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 36.61/24.08  tff(c_535, plain, (![A_53, A_54, B_55, C_56]: (r1_tarski(k8_relat_1(A_53, k8_relat_1(A_54, k8_relat_1(B_55, C_56))), C_56) | ~v1_relat_1(C_56) | ~v1_relat_1(C_56) | ~v1_relat_1(C_56))), inference(superposition, [status(thm), theory('equality')], [c_16, c_228])).
% 36.61/24.08  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.61/24.08  tff(c_2686, plain, (![A_122, A_123, B_124, C_125]: (k3_xboole_0(k8_relat_1(A_122, k8_relat_1(A_123, k8_relat_1(B_124, C_125))), C_125)=k8_relat_1(A_122, k8_relat_1(A_123, k8_relat_1(B_124, C_125))) | ~v1_relat_1(C_125))), inference(resolution, [status(thm)], [c_535, c_8])).
% 36.61/24.08  tff(c_5392, plain, (![A_152, B_153, C_154]: (k8_relat_1(A_152, k8_relat_1(B_153, k8_relat_1(B_153, C_154)))=k3_xboole_0(k8_relat_1(A_152, k8_relat_1(B_153, C_154)), C_154) | ~v1_relat_1(C_154) | ~v1_relat_1(C_154))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2686])).
% 36.61/24.08  tff(c_13893, plain, (![A_202, B_203, C_204]: (v1_relat_1(k3_xboole_0(k8_relat_1(A_202, k8_relat_1(B_203, C_204)), C_204)) | ~v1_relat_1(k8_relat_1(B_203, k8_relat_1(B_203, C_204))) | ~v1_relat_1(C_204) | ~v1_relat_1(C_204))), inference(superposition, [status(thm), theory('equality')], [c_5392, c_12])).
% 36.61/24.08  tff(c_14023, plain, (![A_205, B_206, C_207]: (v1_relat_1(k3_xboole_0(k8_relat_1(A_205, k8_relat_1(B_206, C_207)), C_207)) | ~v1_relat_1(C_207))), inference(resolution, [status(thm)], [c_101, c_13893])).
% 36.61/24.08  tff(c_14207, plain, (![B_2, C_32]: (v1_relat_1(k3_xboole_0(k8_relat_1(B_2, C_32), C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_113, c_14023])).
% 36.61/24.08  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.61/24.08  tff(c_34, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_26])).
% 36.61/24.08  tff(c_110, plain, (![C_32]: (k8_relat_1('#skF_1', k8_relat_1('#skF_2', C_32))=k8_relat_1('#skF_1', C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_34, c_86])).
% 36.61/24.08  tff(c_57, plain, (![A_22, B_23]: (r1_tarski(k8_relat_1(A_22, B_23), B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.61/24.08  tff(c_61, plain, (![A_22, B_23]: (k3_xboole_0(k8_relat_1(A_22, B_23), B_23)=k8_relat_1(A_22, B_23) | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_57, c_8])).
% 36.61/24.08  tff(c_287, plain, (![A_47, B_48, C_49]: (k3_xboole_0(k8_relat_1(A_47, k8_relat_1(B_48, C_49)), C_49)=k8_relat_1(A_47, k8_relat_1(B_48, C_49)) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_228, c_8])).
% 36.61/24.08  tff(c_308, plain, (![B_2, C_32]: (k8_relat_1(B_2, k8_relat_1(B_2, C_32))=k3_xboole_0(k8_relat_1(B_2, C_32), C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_113, c_287])).
% 36.61/24.08  tff(c_24055, plain, (![A_294, B_295, C_296]: (r1_tarski(k8_relat_1(A_294, k3_xboole_0(k8_relat_1(B_295, C_296), C_296)), C_296) | ~v1_relat_1(C_296) | ~v1_relat_1(C_296) | ~v1_relat_1(C_296) | ~v1_relat_1(C_296) | ~v1_relat_1(C_296))), inference(superposition, [status(thm), theory('equality')], [c_308, c_535])).
% 36.61/24.08  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.61/24.08  tff(c_27758, plain, (![A_322, B_323, C_324]: (k8_relat_1(A_322, k3_xboole_0(k8_relat_1(B_323, C_324), C_324))=C_324 | ~r1_tarski(C_324, k8_relat_1(A_322, k3_xboole_0(k8_relat_1(B_323, C_324), C_324))) | ~v1_relat_1(C_324))), inference(resolution, [status(thm)], [c_24055, c_2])).
% 36.61/24.08  tff(c_32538, plain, (![A_358, A_359, B_360]: (k8_relat_1(A_358, k3_xboole_0(k8_relat_1(A_359, B_360), B_360))=B_360 | ~r1_tarski(B_360, k8_relat_1(A_358, k8_relat_1(A_359, B_360))) | ~v1_relat_1(B_360) | ~v1_relat_1(B_360))), inference(superposition, [status(thm), theory('equality')], [c_61, c_27758])).
% 36.61/24.08  tff(c_34464, plain, (![C_367]: (k8_relat_1('#skF_1', k3_xboole_0(k8_relat_1('#skF_2', C_367), C_367))=C_367 | ~r1_tarski(C_367, k8_relat_1('#skF_1', C_367)) | ~v1_relat_1(C_367) | ~v1_relat_1(C_367) | ~v1_relat_1(C_367))), inference(superposition, [status(thm), theory('equality')], [c_110, c_32538])).
% 36.61/24.08  tff(c_24210, plain, (![A_294, B_295, C_296]: (k8_relat_1(A_294, k3_xboole_0(k8_relat_1(B_295, C_296), C_296))=C_296 | ~r1_tarski(C_296, k8_relat_1(A_294, k3_xboole_0(k8_relat_1(B_295, C_296), C_296))) | ~v1_relat_1(C_296))), inference(resolution, [status(thm)], [c_24055, c_2])).
% 36.61/24.08  tff(c_34531, plain, (![C_367]: (k8_relat_1('#skF_1', k3_xboole_0(k8_relat_1('#skF_2', C_367), C_367))=C_367 | ~r1_tarski(C_367, C_367) | ~v1_relat_1(C_367) | ~r1_tarski(C_367, k8_relat_1('#skF_1', C_367)) | ~v1_relat_1(C_367) | ~v1_relat_1(C_367) | ~v1_relat_1(C_367))), inference(superposition, [status(thm), theory('equality')], [c_34464, c_24210])).
% 36.61/24.08  tff(c_34989, plain, (![C_368]: (k8_relat_1('#skF_1', k3_xboole_0(k8_relat_1('#skF_2', C_368), C_368))=C_368 | ~r1_tarski(C_368, k8_relat_1('#skF_1', C_368)) | ~v1_relat_1(C_368))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34531])).
% 36.61/24.08  tff(c_111298, plain, (![C_618]: (r1_tarski(C_618, k3_xboole_0(k8_relat_1('#skF_2', C_618), C_618)) | ~v1_relat_1(k3_xboole_0(k8_relat_1('#skF_2', C_618), C_618)) | ~r1_tarski(C_618, k8_relat_1('#skF_1', C_618)) | ~v1_relat_1(C_618))), inference(superposition, [status(thm), theory('equality')], [c_34989, c_14])).
% 36.61/24.08  tff(c_62, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.61/24.08  tff(c_69, plain, (![A_9, B_10]: (k8_relat_1(A_9, B_10)=B_10 | ~r1_tarski(B_10, k8_relat_1(A_9, B_10)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_14, c_62])).
% 36.61/24.08  tff(c_2057, plain, (![A_100, B_101, C_102]: (k8_relat_1(k3_xboole_0(A_100, B_101), C_102)=C_102 | ~r1_tarski(C_102, k8_relat_1(A_100, k8_relat_1(B_101, C_102))) | ~v1_relat_1(C_102) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_86, c_69])).
% 36.61/24.08  tff(c_2087, plain, (![B_2, C_32]: (k8_relat_1(k3_xboole_0(B_2, B_2), C_32)=C_32 | ~r1_tarski(C_32, k3_xboole_0(k8_relat_1(B_2, C_32), C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_308, c_2057])).
% 36.61/24.08  tff(c_2118, plain, (![B_2, C_32]: (k8_relat_1(B_2, C_32)=C_32 | ~r1_tarski(C_32, k3_xboole_0(k8_relat_1(B_2, C_32), C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_2087])).
% 36.61/24.08  tff(c_112692, plain, (![C_621]: (k8_relat_1('#skF_2', C_621)=C_621 | ~v1_relat_1(k3_xboole_0(k8_relat_1('#skF_2', C_621), C_621)) | ~r1_tarski(C_621, k8_relat_1('#skF_1', C_621)) | ~v1_relat_1(C_621))), inference(resolution, [status(thm)], [c_111298, c_2118])).
% 36.61/24.08  tff(c_112820, plain, (![C_622]: (k8_relat_1('#skF_2', C_622)=C_622 | ~r1_tarski(C_622, k8_relat_1('#skF_1', C_622)) | ~v1_relat_1(C_622))), inference(resolution, [status(thm)], [c_14207, c_112692])).
% 36.61/24.08  tff(c_113009, plain, (![C_32]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', C_32))=k8_relat_1('#skF_1', C_32) | ~r1_tarski(k8_relat_1('#skF_1', C_32), k8_relat_1('#skF_1', C_32)) | ~v1_relat_1(k8_relat_1('#skF_1', C_32)) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_113, c_112820])).
% 36.61/24.08  tff(c_113018, plain, (![C_623]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', C_623))=k8_relat_1('#skF_1', C_623) | ~v1_relat_1(k8_relat_1('#skF_1', C_623)) | ~v1_relat_1(C_623))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_113009])).
% 36.61/24.08  tff(c_113308, plain, (![B_624]: (k8_relat_1('#skF_2', k8_relat_1('#skF_1', B_624))=k8_relat_1('#skF_1', B_624) | ~v1_relat_1(B_624))), inference(resolution, [status(thm)], [c_12, c_113018])).
% 36.61/24.08  tff(c_18, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.61/24.08  tff(c_114421, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_113308, c_18])).
% 36.61/24.08  tff(c_114739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_114421])).
% 36.61/24.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 36.61/24.08  
% 36.61/24.08  Inference rules
% 36.61/24.08  ----------------------
% 36.61/24.08  #Ref     : 0
% 36.61/24.08  #Sup     : 34508
% 36.61/24.08  #Fact    : 0
% 36.61/24.08  #Define  : 0
% 36.61/24.08  #Split   : 2
% 36.61/24.08  #Chain   : 0
% 36.61/24.08  #Close   : 0
% 36.61/24.08  
% 36.61/24.08  Ordering : KBO
% 36.61/24.08  
% 36.61/24.08  Simplification rules
% 36.61/24.08  ----------------------
% 36.61/24.08  #Subsume      : 6962
% 36.61/24.08  #Demod        : 3147
% 36.61/24.08  #Tautology    : 820
% 36.61/24.08  #SimpNegUnit  : 0
% 36.61/24.08  #BackRed      : 0
% 36.61/24.08  
% 36.61/24.08  #Partial instantiations: 0
% 36.61/24.08  #Strategies tried      : 1
% 36.61/24.08  
% 36.61/24.08  Timing (in seconds)
% 36.61/24.08  ----------------------
% 36.61/24.09  Preprocessing        : 0.28
% 36.61/24.09  Parsing              : 0.15
% 36.61/24.09  CNF conversion       : 0.02
% 36.61/24.09  Main loop            : 23.04
% 36.61/24.09  Inferencing          : 4.20
% 36.61/24.09  Reduction            : 3.59
% 36.61/24.09  Demodulation         : 2.46
% 36.61/24.09  BG Simplification    : 0.88
% 36.61/24.09  Subsumption          : 13.47
% 36.61/24.09  Abstraction          : 0.96
% 36.61/24.09  MUC search           : 0.00
% 36.61/24.09  Cooper               : 0.00
% 36.61/24.09  Total                : 23.35
% 36.61/24.09  Index Insertion      : 0.00
% 36.61/24.09  Index Deletion       : 0.00
% 36.61/24.09  Index Matching       : 0.00
% 36.61/24.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
