%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 8.60s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 160 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 176 expanded)
%              Number of equality atoms :   56 ( 119 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_272,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_280,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_272,c_26])).

tff(c_115,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_12])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_34] : r1_tarski(k1_xboole_0,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_24])).

tff(c_281,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_340,plain,(
    ! [A_47] : k3_xboole_0(k1_xboole_0,A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_281])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_349,plain,(
    ! [A_47] : k3_xboole_0(A_47,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_319,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_337,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_319])).

tff(c_585,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_337])).

tff(c_417,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_736,plain,(
    ! [A_63,B_64,C_65] : r1_tarski(k4_xboole_0(A_63,k2_xboole_0(B_64,C_65)),k4_xboole_0(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_16])).

tff(c_844,plain,(
    ! [A_67,C_68] : r1_tarski(k4_xboole_0(A_67,k2_xboole_0(A_67,C_68)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_736])).

tff(c_876,plain,(
    ! [A_69,B_70] : r1_tarski(k4_xboole_0(A_69,k2_xboole_0(B_70,A_69)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_844])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_879,plain,(
    ! [A_69,B_70] : k3_xboole_0(k4_xboole_0(A_69,k2_xboole_0(B_70,A_69)),k1_xboole_0) = k4_xboole_0(A_69,k2_xboole_0(B_70,A_69)) ),
    inference(resolution,[status(thm)],[c_876,c_14])).

tff(c_903,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(B_70,A_69)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_879])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1715,plain,(
    ! [A_86,B_87,C_88] : k4_xboole_0(A_86,k2_xboole_0(k4_xboole_0(A_86,B_87),C_88)) = k4_xboole_0(k3_xboole_0(A_86,B_87),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_417])).

tff(c_1782,plain,(
    ! [A_69,B_87] : k4_xboole_0(k3_xboole_0(A_69,B_87),A_69) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_903,c_1715])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_305,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_281])).

tff(c_68,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_14] : r1_tarski(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_303,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_71,c_281])).

tff(c_467,plain,(
    ! [A_52,B_53] : r1_tarski(k3_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_16])).

tff(c_502,plain,(
    ! [B_54,A_55] : r1_tarski(k3_xboole_0(B_54,A_55),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_467])).

tff(c_10274,plain,(
    ! [B_241,A_242] : k3_xboole_0(k3_xboole_0(B_241,A_242),A_242) = k3_xboole_0(B_241,A_242) ),
    inference(resolution,[status(thm)],[c_502,c_14])).

tff(c_11947,plain,(
    ! [A_252,B_253] : k3_xboole_0(k3_xboole_0(A_252,B_253),A_252) = k3_xboole_0(B_253,A_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10274])).

tff(c_12222,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_11947])).

tff(c_12315,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_12222])).

tff(c_681,plain,(
    ! [A_61,B_62] : k3_xboole_0(k4_xboole_0(A_61,B_62),A_61) = k4_xboole_0(A_61,B_62) ),
    inference(resolution,[status(thm)],[c_16,c_281])).

tff(c_1297,plain,(
    ! [B_79,B_80] : k3_xboole_0(B_79,k4_xboole_0(B_79,B_80)) = k4_xboole_0(B_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_681])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_221,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_225,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_1059,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,k4_xboole_0(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_319])).

tff(c_1123,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_1059])).

tff(c_1146,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1123])).

tff(c_1312,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1297,c_1146])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1390,plain,(
    ! [C_17] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_17)) = k4_xboole_0('#skF_2',C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_1312,c_20])).

tff(c_15873,plain,(
    ! [A_280,B_281,B_282] : k4_xboole_0(A_280,k2_xboole_0(B_281,k4_xboole_0(A_280,B_282))) = k4_xboole_0(k3_xboole_0(A_280,B_282),B_281) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1715])).

tff(c_16155,plain,(
    ! [B_282] : k4_xboole_0(k3_xboole_0('#skF_2',B_282),'#skF_3') = k4_xboole_0('#skF_2',k4_xboole_0('#skF_2',B_282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_15873])).

tff(c_17664,plain,(
    ! [B_290] : k4_xboole_0(k3_xboole_0('#skF_2',B_290),'#skF_3') = k3_xboole_0('#skF_2',B_290) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16155])).

tff(c_17787,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12315,c_17664])).

tff(c_17877,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_4,c_17787])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1820,plain,(
    ! [A_86,B_87] : k4_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1715])).

tff(c_1846,plain,(
    ! [A_86,B_87] : k4_xboole_0(k3_xboole_0(A_86,B_87),k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1820])).

tff(c_17928,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17877,c_1846])).

tff(c_18010,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1782,c_17928])).

tff(c_18012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_18010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.60/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.08  
% 8.60/3.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.09  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.60/3.09  
% 8.60/3.09  %Foreground sorts:
% 8.60/3.09  
% 8.60/3.09  
% 8.60/3.09  %Background operators:
% 8.60/3.09  
% 8.60/3.09  
% 8.60/3.09  %Foreground operators:
% 8.60/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.60/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.60/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.60/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.60/3.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.60/3.09  tff('#skF_2', type, '#skF_2': $i).
% 8.60/3.09  tff('#skF_3', type, '#skF_3': $i).
% 8.60/3.09  tff('#skF_1', type, '#skF_1': $i).
% 8.60/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.60/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.60/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.60/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.60/3.09  
% 8.60/3.10  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.60/3.10  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.60/3.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.60/3.10  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.60/3.10  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.60/3.10  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.60/3.10  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.60/3.10  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.60/3.10  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.60/3.10  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.60/3.10  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.60/3.10  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.60/3.10  tff(c_272, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.60/3.10  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.60/3.10  tff(c_280, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_272, c_26])).
% 8.60/3.10  tff(c_115, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.60/3.10  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.60/3.10  tff(c_168, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_115, c_12])).
% 8.60/3.10  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.60/3.10  tff(c_180, plain, (![A_34]: (r1_tarski(k1_xboole_0, A_34))), inference(superposition, [status(thm), theory('equality')], [c_168, c_24])).
% 8.60/3.10  tff(c_281, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.60/3.10  tff(c_340, plain, (![A_47]: (k3_xboole_0(k1_xboole_0, A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_281])).
% 8.60/3.10  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.60/3.10  tff(c_349, plain, (![A_47]: (k3_xboole_0(A_47, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_340, c_4])).
% 8.60/3.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.60/3.10  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.60/3.10  tff(c_319, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.60/3.10  tff(c_337, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_319])).
% 8.60/3.10  tff(c_585, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_337])).
% 8.60/3.10  tff(c_417, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.60/3.10  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.10  tff(c_736, plain, (![A_63, B_64, C_65]: (r1_tarski(k4_xboole_0(A_63, k2_xboole_0(B_64, C_65)), k4_xboole_0(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_16])).
% 8.60/3.10  tff(c_844, plain, (![A_67, C_68]: (r1_tarski(k4_xboole_0(A_67, k2_xboole_0(A_67, C_68)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_585, c_736])).
% 8.60/3.10  tff(c_876, plain, (![A_69, B_70]: (r1_tarski(k4_xboole_0(A_69, k2_xboole_0(B_70, A_69)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_844])).
% 8.60/3.10  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.60/3.10  tff(c_879, plain, (![A_69, B_70]: (k3_xboole_0(k4_xboole_0(A_69, k2_xboole_0(B_70, A_69)), k1_xboole_0)=k4_xboole_0(A_69, k2_xboole_0(B_70, A_69)))), inference(resolution, [status(thm)], [c_876, c_14])).
% 8.60/3.10  tff(c_903, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(B_70, A_69))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_879])).
% 8.60/3.10  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.60/3.10  tff(c_1715, plain, (![A_86, B_87, C_88]: (k4_xboole_0(A_86, k2_xboole_0(k4_xboole_0(A_86, B_87), C_88))=k4_xboole_0(k3_xboole_0(A_86, B_87), C_88))), inference(superposition, [status(thm), theory('equality')], [c_22, c_417])).
% 8.60/3.10  tff(c_1782, plain, (![A_69, B_87]: (k4_xboole_0(k3_xboole_0(A_69, B_87), A_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_903, c_1715])).
% 8.60/3.10  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.60/3.10  tff(c_305, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_30, c_281])).
% 8.60/3.10  tff(c_68, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.10  tff(c_71, plain, (![A_14]: (r1_tarski(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_68])).
% 8.60/3.10  tff(c_303, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(resolution, [status(thm)], [c_71, c_281])).
% 8.60/3.10  tff(c_467, plain, (![A_52, B_53]: (r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_319, c_16])).
% 8.60/3.10  tff(c_502, plain, (![B_54, A_55]: (r1_tarski(k3_xboole_0(B_54, A_55), A_55))), inference(superposition, [status(thm), theory('equality')], [c_4, c_467])).
% 8.60/3.10  tff(c_10274, plain, (![B_241, A_242]: (k3_xboole_0(k3_xboole_0(B_241, A_242), A_242)=k3_xboole_0(B_241, A_242))), inference(resolution, [status(thm)], [c_502, c_14])).
% 8.60/3.10  tff(c_11947, plain, (![A_252, B_253]: (k3_xboole_0(k3_xboole_0(A_252, B_253), A_252)=k3_xboole_0(B_253, A_252))), inference(superposition, [status(thm), theory('equality')], [c_4, c_10274])).
% 8.60/3.10  tff(c_12222, plain, (k3_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_305, c_11947])).
% 8.60/3.10  tff(c_12315, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_12222])).
% 8.60/3.10  tff(c_681, plain, (![A_61, B_62]: (k3_xboole_0(k4_xboole_0(A_61, B_62), A_61)=k4_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_16, c_281])).
% 8.60/3.10  tff(c_1297, plain, (![B_79, B_80]: (k3_xboole_0(B_79, k4_xboole_0(B_79, B_80))=k4_xboole_0(B_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_4, c_681])).
% 8.60/3.10  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.60/3.10  tff(c_221, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.60/3.10  tff(c_225, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_221])).
% 8.60/3.10  tff(c_1059, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k3_xboole_0(A_75, k4_xboole_0(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_319])).
% 8.60/3.10  tff(c_1123, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_225, c_1059])).
% 8.60/3.10  tff(c_1146, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1123])).
% 8.60/3.10  tff(c_1312, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1297, c_1146])).
% 8.60/3.10  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.60/3.10  tff(c_1390, plain, (![C_17]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_17))=k4_xboole_0('#skF_2', C_17))), inference(superposition, [status(thm), theory('equality')], [c_1312, c_20])).
% 8.60/3.10  tff(c_15873, plain, (![A_280, B_281, B_282]: (k4_xboole_0(A_280, k2_xboole_0(B_281, k4_xboole_0(A_280, B_282)))=k4_xboole_0(k3_xboole_0(A_280, B_282), B_281))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1715])).
% 8.60/3.10  tff(c_16155, plain, (![B_282]: (k4_xboole_0(k3_xboole_0('#skF_2', B_282), '#skF_3')=k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', B_282)))), inference(superposition, [status(thm), theory('equality')], [c_1390, c_15873])).
% 8.60/3.10  tff(c_17664, plain, (![B_290]: (k4_xboole_0(k3_xboole_0('#skF_2', B_290), '#skF_3')=k3_xboole_0('#skF_2', B_290))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16155])).
% 8.60/3.10  tff(c_17787, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12315, c_17664])).
% 8.60/3.10  tff(c_17877, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_4, c_17787])).
% 8.60/3.10  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.60/3.10  tff(c_1820, plain, (![A_86, B_87]: (k4_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=k4_xboole_0(A_86, k4_xboole_0(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1715])).
% 8.60/3.10  tff(c_1846, plain, (![A_86, B_87]: (k4_xboole_0(k3_xboole_0(A_86, B_87), k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1820])).
% 8.60/3.10  tff(c_17928, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17877, c_1846])).
% 8.60/3.10  tff(c_18010, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1782, c_17928])).
% 8.60/3.10  tff(c_18012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_18010])).
% 8.60/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/3.10  
% 8.60/3.10  Inference rules
% 8.60/3.10  ----------------------
% 8.60/3.10  #Ref     : 0
% 8.60/3.10  #Sup     : 4355
% 8.60/3.10  #Fact    : 0
% 8.60/3.10  #Define  : 0
% 8.60/3.10  #Split   : 0
% 8.60/3.10  #Chain   : 0
% 8.60/3.10  #Close   : 0
% 8.60/3.10  
% 8.60/3.10  Ordering : KBO
% 8.60/3.10  
% 8.60/3.10  Simplification rules
% 8.60/3.10  ----------------------
% 8.60/3.10  #Subsume      : 18
% 8.60/3.10  #Demod        : 5155
% 8.60/3.10  #Tautology    : 3384
% 8.60/3.10  #SimpNegUnit  : 1
% 8.60/3.10  #BackRed      : 8
% 8.60/3.10  
% 8.60/3.10  #Partial instantiations: 0
% 8.60/3.10  #Strategies tried      : 1
% 8.60/3.10  
% 8.60/3.10  Timing (in seconds)
% 8.60/3.10  ----------------------
% 8.60/3.11  Preprocessing        : 0.28
% 8.60/3.11  Parsing              : 0.16
% 8.60/3.11  CNF conversion       : 0.02
% 8.60/3.11  Main loop            : 2.07
% 8.60/3.11  Inferencing          : 0.46
% 8.60/3.11  Reduction            : 1.17
% 8.60/3.11  Demodulation         : 1.02
% 8.60/3.11  BG Simplification    : 0.05
% 8.60/3.11  Subsumption          : 0.29
% 8.60/3.11  Abstraction          : 0.08
% 8.60/3.11  MUC search           : 0.00
% 8.60/3.11  Cooper               : 0.00
% 8.60/3.11  Total                : 2.38
% 8.60/3.11  Index Insertion      : 0.00
% 8.60/3.11  Index Deletion       : 0.00
% 8.60/3.11  Index Matching       : 0.00
% 8.60/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
