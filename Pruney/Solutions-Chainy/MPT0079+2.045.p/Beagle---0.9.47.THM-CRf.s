%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:48 EST 2020

% Result     : Theorem 11.03s
% Output     : CNFRefutation 11.03s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 312 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 412 expanded)
%              Number of equality atoms :   72 ( 275 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_36,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    r1_xboole_0('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1043,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1062,plain,(
    ! [C_93] :
      ( ~ r2_hidden(C_93,'#skF_5')
      | ~ r2_hidden(C_93,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_1043])).

tff(c_2340,plain,(
    ! [A_121] :
      ( ~ r2_hidden('#skF_1'(A_121,'#skF_7'),'#skF_5')
      | r1_xboole_0(A_121,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_1062])).

tff(c_2345,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_2340])).

tff(c_16,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    ! [A_41,B_42] :
      ( ~ r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_106])).

tff(c_2352,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2345,c_114])).

tff(c_28,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2374,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_28])).

tff(c_2392,plain,(
    k4_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2374])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,(
    ! [A_45,B_46] :
      ( ~ r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_106])).

tff(c_131,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_123])).

tff(c_199,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_211,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_199])).

tff(c_18,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_217,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_17,k1_xboole_0)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_199])).

tff(c_223,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_217])).

tff(c_349,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_223])).

tff(c_225,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_217])).

tff(c_253,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_225])).

tff(c_42,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_414,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_445,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_414])).

tff(c_452,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_445])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1179,plain,(
    ! [A_97,B_98,C_99] : k2_xboole_0(k2_xboole_0(A_97,B_98),C_99) = k2_xboole_0(A_97,k2_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1302,plain,(
    ! [A_100,C_101] : k2_xboole_0(A_100,k2_xboole_0(A_100,C_101)) = k2_xboole_0(A_100,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1179])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1328,plain,(
    ! [A_100,C_101] : k4_xboole_0(k2_xboole_0(A_100,C_101),k2_xboole_0(A_100,C_101)) = k4_xboole_0(A_100,k2_xboole_0(A_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_24])).

tff(c_1409,plain,(
    ! [A_102,C_103] : k4_xboole_0(A_102,k2_xboole_0(A_102,C_103)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_1328])).

tff(c_1455,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1409])).

tff(c_2130,plain,(
    ! [A_117,B_118,C_119] : k4_xboole_0(k4_xboole_0(A_117,B_118),C_119) = k4_xboole_0(A_117,k2_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_25458,plain,(
    ! [C_343,A_344,B_345] : k2_xboole_0(C_343,k4_xboole_0(A_344,k2_xboole_0(B_345,C_343))) = k2_xboole_0(C_343,k4_xboole_0(A_344,B_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2130,c_20])).

tff(c_25787,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1455,c_25458])).

tff(c_25940,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_349,c_253,c_25787])).

tff(c_633,plain,(
    ! [A_70,B_71] : k4_xboole_0(k2_xboole_0(A_70,B_71),B_71) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_667,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_7') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_633])).

tff(c_5792,plain,(
    ! [B_171,A_172,B_173] : k2_xboole_0(B_171,k2_xboole_0(A_172,B_173)) = k2_xboole_0(A_172,k2_xboole_0(B_173,B_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1179])).

tff(c_6101,plain,(
    ! [B_171] : k2_xboole_0(B_171,k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_6',k2_xboole_0('#skF_7',B_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5792])).

tff(c_10139,plain,(
    ! [A_219,A_220] : k2_xboole_0(A_219,k2_xboole_0(A_220,A_219)) = k2_xboole_0(A_220,A_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5792])).

tff(c_10295,plain,(
    k2_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6101,c_10139])).

tff(c_10418,plain,(
    k2_xboole_0('#skF_6',k2_xboole_0('#skF_5','#skF_7')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10295])).

tff(c_26553,plain,(
    ! [A_347,B_348,C_349] : k4_xboole_0(k2_xboole_0(A_347,k2_xboole_0(B_348,C_349)),C_349) = k4_xboole_0(k2_xboole_0(A_347,B_348),C_349) ),
    inference(superposition,[status(thm),theory(equality)],[c_1179,c_24])).

tff(c_26768,plain,(
    k4_xboole_0(k2_xboole_0('#skF_6','#skF_5'),'#skF_7') = k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10418,c_26553])).

tff(c_26986,plain,(
    k4_xboole_0('#skF_6','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_25940,c_667,c_26768])).

tff(c_26,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k4_xboole_0(A_23,B_24),C_25) = k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2229,plain,(
    ! [A_26,B_27,C_119] : k4_xboole_0(A_26,k2_xboole_0(k3_xboole_0(A_26,B_27),C_119)) = k4_xboole_0(k4_xboole_0(A_26,B_27),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2130])).

tff(c_19788,plain,(
    ! [A_291,B_292,C_293] : k4_xboole_0(A_291,k2_xboole_0(k3_xboole_0(A_291,B_292),C_293)) = k4_xboole_0(A_291,k2_xboole_0(B_292,C_293)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2229])).

tff(c_20175,plain,(
    ! [C_293] : k4_xboole_0('#skF_6',k2_xboole_0(k1_xboole_0,C_293)) = k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_19788])).

tff(c_25048,plain,(
    ! [C_342] : k4_xboole_0('#skF_6',k2_xboole_0('#skF_4',C_342)) = k4_xboole_0('#skF_6',C_342) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_20175])).

tff(c_25172,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25048,c_1455])).

tff(c_30,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_25417,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k3_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_25172,c_30])).

tff(c_25454,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_25417])).

tff(c_433,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_414])).

tff(c_2569,plain,(
    ! [A_28,B_29] : k3_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_433])).

tff(c_27099,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26986,c_2569])).

tff(c_27133,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26986,c_25454,c_27099])).

tff(c_27135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_27133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:34:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.03/4.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.84  
% 11.03/4.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.84  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 11.03/4.84  
% 11.03/4.84  %Foreground sorts:
% 11.03/4.84  
% 11.03/4.84  
% 11.03/4.84  %Background operators:
% 11.03/4.84  
% 11.03/4.84  
% 11.03/4.84  %Foreground operators:
% 11.03/4.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.03/4.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.03/4.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.03/4.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.03/4.84  tff('#skF_7', type, '#skF_7': $i).
% 11.03/4.84  tff('#skF_5', type, '#skF_5': $i).
% 11.03/4.84  tff('#skF_6', type, '#skF_6': $i).
% 11.03/4.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.03/4.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.03/4.84  tff('#skF_4', type, '#skF_4': $i).
% 11.03/4.84  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.03/4.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.03/4.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.03/4.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.03/4.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.03/4.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.03/4.84  
% 11.03/4.86  tff(f_96, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 11.03/4.86  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.03/4.86  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.03/4.86  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.03/4.86  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.03/4.86  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.03/4.86  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.03/4.86  tff(f_87, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.03/4.86  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 11.03/4.86  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.03/4.86  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.03/4.86  tff(f_85, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.03/4.86  tff(f_77, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.03/4.86  tff(f_79, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.03/4.86  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.03/4.86  tff(c_36, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.86  tff(c_22, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.03/4.86  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.86  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.86  tff(c_38, plain, (r1_xboole_0('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.86  tff(c_1043, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.86  tff(c_1062, plain, (![C_93]: (~r2_hidden(C_93, '#skF_5') | ~r2_hidden(C_93, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_1043])).
% 11.03/4.86  tff(c_2340, plain, (![A_121]: (~r2_hidden('#skF_1'(A_121, '#skF_7'), '#skF_5') | r1_xboole_0(A_121, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_1062])).
% 11.03/4.86  tff(c_2345, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_2340])).
% 11.03/4.86  tff(c_16, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.03/4.86  tff(c_106, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.03/4.86  tff(c_114, plain, (![A_41, B_42]: (~r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_106])).
% 11.03/4.86  tff(c_2352, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_2345, c_114])).
% 11.03/4.86  tff(c_28, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.03/4.86  tff(c_2374, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2352, c_28])).
% 11.03/4.86  tff(c_2392, plain, (k4_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2374])).
% 11.03/4.86  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.03/4.86  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.86  tff(c_123, plain, (![A_45, B_46]: (~r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_106])).
% 11.03/4.86  tff(c_131, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_123])).
% 11.03/4.86  tff(c_199, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_87])).
% 11.03/4.86  tff(c_211, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_131, c_199])).
% 11.03/4.86  tff(c_18, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.03/4.86  tff(c_217, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_17, k1_xboole_0))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_18, c_199])).
% 11.03/4.86  tff(c_223, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_217])).
% 11.03/4.86  tff(c_349, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_211, c_223])).
% 11.03/4.86  tff(c_225, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_217])).
% 11.03/4.86  tff(c_253, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_225])).
% 11.03/4.86  tff(c_42, plain, (k2_xboole_0('#skF_6', '#skF_7')=k2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.86  tff(c_414, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.03/4.86  tff(c_445, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_414])).
% 11.03/4.86  tff(c_452, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_445])).
% 11.03/4.86  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.03/4.86  tff(c_1179, plain, (![A_97, B_98, C_99]: (k2_xboole_0(k2_xboole_0(A_97, B_98), C_99)=k2_xboole_0(A_97, k2_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.03/4.86  tff(c_1302, plain, (![A_100, C_101]: (k2_xboole_0(A_100, k2_xboole_0(A_100, C_101))=k2_xboole_0(A_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1179])).
% 11.03/4.86  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.03/4.86  tff(c_1328, plain, (![A_100, C_101]: (k4_xboole_0(k2_xboole_0(A_100, C_101), k2_xboole_0(A_100, C_101))=k4_xboole_0(A_100, k2_xboole_0(A_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_1302, c_24])).
% 11.03/4.86  tff(c_1409, plain, (![A_102, C_103]: (k4_xboole_0(A_102, k2_xboole_0(A_102, C_103))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_452, c_1328])).
% 11.03/4.86  tff(c_1455, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_1409])).
% 11.03/4.86  tff(c_2130, plain, (![A_117, B_118, C_119]: (k4_xboole_0(k4_xboole_0(A_117, B_118), C_119)=k4_xboole_0(A_117, k2_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.03/4.86  tff(c_20, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.03/4.86  tff(c_25458, plain, (![C_343, A_344, B_345]: (k2_xboole_0(C_343, k4_xboole_0(A_344, k2_xboole_0(B_345, C_343)))=k2_xboole_0(C_343, k4_xboole_0(A_344, B_345)))), inference(superposition, [status(thm), theory('equality')], [c_2130, c_20])).
% 11.03/4.86  tff(c_25787, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1455, c_25458])).
% 11.03/4.86  tff(c_25940, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_349, c_253, c_25787])).
% 11.03/4.86  tff(c_633, plain, (![A_70, B_71]: (k4_xboole_0(k2_xboole_0(A_70, B_71), B_71)=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.03/4.86  tff(c_667, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_7')=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_42, c_633])).
% 11.03/4.86  tff(c_5792, plain, (![B_171, A_172, B_173]: (k2_xboole_0(B_171, k2_xboole_0(A_172, B_173))=k2_xboole_0(A_172, k2_xboole_0(B_173, B_171)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1179])).
% 11.03/4.86  tff(c_6101, plain, (![B_171]: (k2_xboole_0(B_171, k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_6', k2_xboole_0('#skF_7', B_171)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5792])).
% 11.03/4.86  tff(c_10139, plain, (![A_219, A_220]: (k2_xboole_0(A_219, k2_xboole_0(A_220, A_219))=k2_xboole_0(A_220, A_219))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5792])).
% 11.03/4.86  tff(c_10295, plain, (k2_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6101, c_10139])).
% 11.03/4.86  tff(c_10418, plain, (k2_xboole_0('#skF_6', k2_xboole_0('#skF_5', '#skF_7'))=k2_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10295])).
% 11.03/4.86  tff(c_26553, plain, (![A_347, B_348, C_349]: (k4_xboole_0(k2_xboole_0(A_347, k2_xboole_0(B_348, C_349)), C_349)=k4_xboole_0(k2_xboole_0(A_347, B_348), C_349))), inference(superposition, [status(thm), theory('equality')], [c_1179, c_24])).
% 11.03/4.86  tff(c_26768, plain, (k4_xboole_0(k2_xboole_0('#skF_6', '#skF_5'), '#skF_7')=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10418, c_26553])).
% 11.03/4.86  tff(c_26986, plain, (k4_xboole_0('#skF_6', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_25940, c_667, c_26768])).
% 11.03/4.86  tff(c_26, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k4_xboole_0(A_23, B_24), C_25)=k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.03/4.86  tff(c_2229, plain, (![A_26, B_27, C_119]: (k4_xboole_0(A_26, k2_xboole_0(k3_xboole_0(A_26, B_27), C_119))=k4_xboole_0(k4_xboole_0(A_26, B_27), C_119))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2130])).
% 11.03/4.86  tff(c_19788, plain, (![A_291, B_292, C_293]: (k4_xboole_0(A_291, k2_xboole_0(k3_xboole_0(A_291, B_292), C_293))=k4_xboole_0(A_291, k2_xboole_0(B_292, C_293)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2229])).
% 11.03/4.86  tff(c_20175, plain, (![C_293]: (k4_xboole_0('#skF_6', k2_xboole_0(k1_xboole_0, C_293))=k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_293)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_19788])).
% 11.03/4.86  tff(c_25048, plain, (![C_342]: (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', C_342))=k4_xboole_0('#skF_6', C_342))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_20175])).
% 11.03/4.86  tff(c_25172, plain, (k4_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25048, c_1455])).
% 11.03/4.86  tff(c_30, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.03/4.86  tff(c_25417, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k3_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_25172, c_30])).
% 11.03/4.86  tff(c_25454, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_25417])).
% 11.03/4.86  tff(c_433, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k3_xboole_0(A_28, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_414])).
% 11.03/4.86  tff(c_2569, plain, (![A_28, B_29]: (k3_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_433])).
% 11.03/4.86  tff(c_27099, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26986, c_2569])).
% 11.03/4.86  tff(c_27133, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_26986, c_25454, c_27099])).
% 11.03/4.86  tff(c_27135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_27133])).
% 11.03/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.86  
% 11.03/4.86  Inference rules
% 11.03/4.86  ----------------------
% 11.03/4.86  #Ref     : 0
% 11.03/4.86  #Sup     : 6817
% 11.03/4.86  #Fact    : 0
% 11.03/4.86  #Define  : 0
% 11.03/4.86  #Split   : 5
% 11.03/4.86  #Chain   : 0
% 11.03/4.86  #Close   : 0
% 11.03/4.86  
% 11.03/4.86  Ordering : KBO
% 11.03/4.86  
% 11.03/4.86  Simplification rules
% 11.03/4.86  ----------------------
% 11.03/4.86  #Subsume      : 117
% 11.03/4.86  #Demod        : 8006
% 11.03/4.86  #Tautology    : 4457
% 11.03/4.86  #SimpNegUnit  : 21
% 11.03/4.86  #BackRed      : 6
% 11.03/4.86  
% 11.03/4.86  #Partial instantiations: 0
% 11.03/4.86  #Strategies tried      : 1
% 11.03/4.86  
% 11.03/4.86  Timing (in seconds)
% 11.03/4.86  ----------------------
% 11.03/4.86  Preprocessing        : 0.30
% 11.03/4.86  Parsing              : 0.16
% 11.03/4.86  CNF conversion       : 0.02
% 11.03/4.86  Main loop            : 3.79
% 11.03/4.86  Inferencing          : 0.69
% 11.03/4.86  Reduction            : 2.26
% 11.03/4.86  Demodulation         : 2.02
% 11.03/4.86  BG Simplification    : 0.08
% 11.03/4.86  Subsumption          : 0.61
% 11.03/4.86  Abstraction          : 0.13
% 11.03/4.86  MUC search           : 0.00
% 11.03/4.86  Cooper               : 0.00
% 11.03/4.86  Total                : 4.13
% 11.03/4.86  Index Insertion      : 0.00
% 11.03/4.86  Index Deletion       : 0.00
% 11.03/4.86  Index Matching       : 0.00
% 11.24/4.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
