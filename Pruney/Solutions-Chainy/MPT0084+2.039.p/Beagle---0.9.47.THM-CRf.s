%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 171 expanded)
%              Number of equality atoms :   56 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k3_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_32])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_360,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_363,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,k4_xboole_0(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_24])).

tff(c_411,plain,(
    ! [A_50,B_51] : k3_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_363])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [A_16] : r1_tarski(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_49])).

tff(c_103,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_103])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [A_42] : r1_tarski(k1_xboole_0,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_18])).

tff(c_98,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2192,plain,(
    ! [A_102,B_103] :
      ( k2_xboole_0(A_102,B_103) = B_103
      | k4_xboole_0(A_102,B_103) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_2256,plain,(
    ! [A_104] :
      ( k2_xboole_0(A_104,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2192])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2305,plain,(
    ! [A_104,C_7] :
      ( r1_tarski(A_104,C_7)
      | ~ r1_tarski(k1_xboole_0,C_7)
      | k1_xboole_0 != A_104 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2256,c_10])).

tff(c_2370,plain,(
    ! [A_105,C_106] :
      ( r1_tarski(A_105,C_106)
      | k1_xboole_0 != A_105 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2305])).

tff(c_2392,plain,(
    ! [A_107,C_108] :
      ( k2_xboole_0(A_107,C_108) = C_108
      | k1_xboole_0 != A_107 ) ),
    inference(resolution,[status(thm)],[c_2370,c_12])).

tff(c_483,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(k2_xboole_0(A_54,B_56),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_537,plain,(
    ! [A_59,B_60] : r1_tarski(A_59,k2_xboole_0(A_59,B_60)) ),
    inference(resolution,[status(thm)],[c_52,c_483])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_773,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_537,c_8])).

tff(c_782,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_24])).

tff(c_820,plain,(
    ! [A_70,B_71] : k3_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_782])).

tff(c_2987,plain,(
    ! [A_114,C_115] :
      ( k3_xboole_0(A_114,C_115) = A_114
      | k1_xboole_0 != A_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_820])).

tff(c_3382,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = A_118
      | k1_xboole_0 != A_118 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_2987])).

tff(c_689,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k3_xboole_0(A_67,B_68),C_69) = k3_xboole_0(A_67,k4_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_508,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_18])).

tff(c_530,plain,(
    ! [A_57,B_58] : k4_xboole_0(k3_xboole_0(A_57,B_58),A_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_508,c_8])).

tff(c_832,plain,(
    ! [C_72,B_73] : k3_xboole_0(C_72,k4_xboole_0(B_73,C_72)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_530])).

tff(c_852,plain,(
    ! [C_72,B_73] : k4_xboole_0(C_72,k4_xboole_0(B_73,C_72)) = k4_xboole_0(C_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_22])).

tff(c_897,plain,(
    ! [C_72,B_73] : k4_xboole_0(C_72,k4_xboole_0(B_73,C_72)) = C_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_852])).

tff(c_3954,plain,(
    ! [B_119] : k4_xboole_0(B_119,k1_xboole_0) = B_119 ),
    inference(superposition,[status(thm),theory(equality)],[c_3382,c_897])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_531,plain,(
    ! [A_57,B_58] : k2_xboole_0(k3_xboole_0(A_57,B_58),A_57) = A_57 ),
    inference(resolution,[status(thm)],[c_508,c_12])).

tff(c_1734,plain,(
    ! [A_89,B_90,B_91] : r1_tarski(A_89,k2_xboole_0(k2_xboole_0(A_89,B_90),B_91)) ),
    inference(resolution,[status(thm)],[c_537,c_10])).

tff(c_1855,plain,(
    ! [A_95,B_96,B_97] : r1_tarski(k3_xboole_0(A_95,B_96),k2_xboole_0(A_95,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_1734])).

tff(c_1952,plain,(
    ! [B_98] : r1_tarski(k3_xboole_0('#skF_1',B_98),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1855])).

tff(c_2044,plain,(
    ! [B_100] : k4_xboole_0(k3_xboole_0('#skF_1',B_100),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1952,c_8])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k4_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2061,plain,(
    ! [B_100] : k3_xboole_0('#skF_1',k4_xboole_0(B_100,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_26])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_120,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_120])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k3_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k3_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_747,plain,(
    ! [A_67,B_68,B_18] : k3_xboole_0(A_67,k4_xboole_0(B_68,k3_xboole_0(k3_xboole_0(A_67,B_68),B_18))) = k4_xboole_0(k3_xboole_0(A_67,B_68),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_689])).

tff(c_769,plain,(
    ! [A_67,B_68,B_18] : k3_xboole_0(A_67,k4_xboole_0(B_68,k3_xboole_0(k3_xboole_0(A_67,B_68),B_18))) = k3_xboole_0(A_67,k4_xboole_0(B_68,B_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_747])).

tff(c_4887,plain,(
    ! [A_143,B_144,B_145] : k3_xboole_0(A_143,k4_xboole_0(B_144,k3_xboole_0(A_143,k3_xboole_0(B_144,B_145)))) = k3_xboole_0(A_143,k4_xboole_0(B_144,B_145)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_769])).

tff(c_5117,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k1_xboole_0)) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4887])).

tff(c_5175,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3954,c_2061,c_5117])).

tff(c_5177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.92  
% 4.67/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.93  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.67/1.93  
% 4.67/1.93  %Foreground sorts:
% 4.67/1.93  
% 4.67/1.93  
% 4.67/1.93  %Background operators:
% 4.67/1.93  
% 4.67/1.93  
% 4.67/1.93  %Foreground operators:
% 4.67/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.67/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.67/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/1.93  
% 4.67/1.94  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.67/1.94  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.67/1.94  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.67/1.94  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.67/1.94  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.67/1.94  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.67/1.94  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.67/1.94  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.67/1.94  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.67/1.94  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.67/1.94  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.67/1.94  tff(c_54, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k3_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.94  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.94  tff(c_58, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_32])).
% 4.67/1.94  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.67/1.94  tff(c_360, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.94  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.94  tff(c_363, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k3_xboole_0(A_50, k4_xboole_0(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_360, c_24])).
% 4.67/1.94  tff(c_411, plain, (![A_50, B_51]: (k3_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_363])).
% 4.67/1.94  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.67/1.94  tff(c_49, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.94  tff(c_52, plain, (![A_16]: (r1_tarski(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_20, c_49])).
% 4.67/1.94  tff(c_103, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.94  tff(c_147, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_103])).
% 4.67/1.94  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.94  tff(c_155, plain, (![A_42]: (r1_tarski(k1_xboole_0, A_42))), inference(superposition, [status(thm), theory('equality')], [c_147, c_18])).
% 4.67/1.94  tff(c_98, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.94  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.94  tff(c_2192, plain, (![A_102, B_103]: (k2_xboole_0(A_102, B_103)=B_103 | k4_xboole_0(A_102, B_103)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_12])).
% 4.67/1.94  tff(c_2256, plain, (![A_104]: (k2_xboole_0(A_104, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_104)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2192])).
% 4.67/1.94  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.67/1.94  tff(c_2305, plain, (![A_104, C_7]: (r1_tarski(A_104, C_7) | ~r1_tarski(k1_xboole_0, C_7) | k1_xboole_0!=A_104)), inference(superposition, [status(thm), theory('equality')], [c_2256, c_10])).
% 4.67/1.94  tff(c_2370, plain, (![A_105, C_106]: (r1_tarski(A_105, C_106) | k1_xboole_0!=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2305])).
% 4.67/1.94  tff(c_2392, plain, (![A_107, C_108]: (k2_xboole_0(A_107, C_108)=C_108 | k1_xboole_0!=A_107)), inference(resolution, [status(thm)], [c_2370, c_12])).
% 4.67/1.94  tff(c_483, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(k2_xboole_0(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.67/1.94  tff(c_537, plain, (![A_59, B_60]: (r1_tarski(A_59, k2_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_52, c_483])).
% 4.67/1.94  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.94  tff(c_773, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k1_xboole_0)), inference(resolution, [status(thm)], [c_537, c_8])).
% 4.67/1.94  tff(c_782, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k4_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_773, c_24])).
% 4.67/1.94  tff(c_820, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k2_xboole_0(A_70, B_71))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_782])).
% 4.67/1.94  tff(c_2987, plain, (![A_114, C_115]: (k3_xboole_0(A_114, C_115)=A_114 | k1_xboole_0!=A_114)), inference(superposition, [status(thm), theory('equality')], [c_2392, c_820])).
% 4.67/1.94  tff(c_3382, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=A_118 | k1_xboole_0!=A_118)), inference(superposition, [status(thm), theory('equality')], [c_411, c_2987])).
% 4.67/1.94  tff(c_689, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k3_xboole_0(A_67, B_68), C_69)=k3_xboole_0(A_67, k4_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.94  tff(c_508, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(superposition, [status(thm), theory('equality')], [c_360, c_18])).
% 4.67/1.94  tff(c_530, plain, (![A_57, B_58]: (k4_xboole_0(k3_xboole_0(A_57, B_58), A_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_508, c_8])).
% 4.67/1.94  tff(c_832, plain, (![C_72, B_73]: (k3_xboole_0(C_72, k4_xboole_0(B_73, C_72))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_689, c_530])).
% 4.67/1.94  tff(c_852, plain, (![C_72, B_73]: (k4_xboole_0(C_72, k4_xboole_0(B_73, C_72))=k4_xboole_0(C_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_832, c_22])).
% 4.67/1.94  tff(c_897, plain, (![C_72, B_73]: (k4_xboole_0(C_72, k4_xboole_0(B_73, C_72))=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_852])).
% 4.67/1.94  tff(c_3954, plain, (![B_119]: (k4_xboole_0(B_119, k1_xboole_0)=B_119)), inference(superposition, [status(thm), theory('equality')], [c_3382, c_897])).
% 4.67/1.94  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.94  tff(c_59, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.94  tff(c_71, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_59])).
% 4.67/1.94  tff(c_531, plain, (![A_57, B_58]: (k2_xboole_0(k3_xboole_0(A_57, B_58), A_57)=A_57)), inference(resolution, [status(thm)], [c_508, c_12])).
% 4.67/1.94  tff(c_1734, plain, (![A_89, B_90, B_91]: (r1_tarski(A_89, k2_xboole_0(k2_xboole_0(A_89, B_90), B_91)))), inference(resolution, [status(thm)], [c_537, c_10])).
% 4.67/1.94  tff(c_1855, plain, (![A_95, B_96, B_97]: (r1_tarski(k3_xboole_0(A_95, B_96), k2_xboole_0(A_95, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_531, c_1734])).
% 4.67/1.94  tff(c_1952, plain, (![B_98]: (r1_tarski(k3_xboole_0('#skF_1', B_98), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1855])).
% 4.67/1.94  tff(c_2044, plain, (![B_100]: (k4_xboole_0(k3_xboole_0('#skF_1', B_100), '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1952, c_8])).
% 4.67/1.94  tff(c_26, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.94  tff(c_2061, plain, (![B_100]: (k3_xboole_0('#skF_1', k4_xboole_0(B_100, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2044, c_26])).
% 4.67/1.94  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.94  tff(c_120, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.67/1.94  tff(c_128, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_120])).
% 4.67/1.94  tff(c_14, plain, (![A_10, B_11, C_12]: (k3_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k3_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.67/1.94  tff(c_747, plain, (![A_67, B_68, B_18]: (k3_xboole_0(A_67, k4_xboole_0(B_68, k3_xboole_0(k3_xboole_0(A_67, B_68), B_18)))=k4_xboole_0(k3_xboole_0(A_67, B_68), B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_689])).
% 4.67/1.94  tff(c_769, plain, (![A_67, B_68, B_18]: (k3_xboole_0(A_67, k4_xboole_0(B_68, k3_xboole_0(k3_xboole_0(A_67, B_68), B_18)))=k3_xboole_0(A_67, k4_xboole_0(B_68, B_18)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_747])).
% 4.67/1.94  tff(c_4887, plain, (![A_143, B_144, B_145]: (k3_xboole_0(A_143, k4_xboole_0(B_144, k3_xboole_0(A_143, k3_xboole_0(B_144, B_145))))=k3_xboole_0(A_143, k4_xboole_0(B_144, B_145)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_769])).
% 4.67/1.94  tff(c_5117, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k1_xboole_0))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_4887])).
% 4.67/1.94  tff(c_5175, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3954, c_2061, c_5117])).
% 4.67/1.94  tff(c_5177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_5175])).
% 4.67/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.94  
% 4.67/1.94  Inference rules
% 4.67/1.94  ----------------------
% 4.67/1.94  #Ref     : 0
% 4.67/1.94  #Sup     : 1315
% 4.67/1.94  #Fact    : 0
% 4.67/1.94  #Define  : 0
% 4.67/1.94  #Split   : 2
% 4.67/1.94  #Chain   : 0
% 4.67/1.94  #Close   : 0
% 4.67/1.94  
% 4.67/1.94  Ordering : KBO
% 4.67/1.94  
% 4.67/1.94  Simplification rules
% 4.67/1.94  ----------------------
% 4.67/1.94  #Subsume      : 214
% 4.67/1.94  #Demod        : 848
% 4.67/1.94  #Tautology    : 811
% 4.67/1.94  #SimpNegUnit  : 37
% 4.67/1.94  #BackRed      : 0
% 4.67/1.94  
% 4.67/1.94  #Partial instantiations: 0
% 4.67/1.94  #Strategies tried      : 1
% 4.67/1.94  
% 4.67/1.94  Timing (in seconds)
% 4.67/1.94  ----------------------
% 4.67/1.94  Preprocessing        : 0.28
% 4.67/1.94  Parsing              : 0.15
% 4.67/1.94  CNF conversion       : 0.02
% 4.67/1.94  Main loop            : 0.88
% 4.67/1.94  Inferencing          : 0.29
% 4.67/1.94  Reduction            : 0.38
% 4.67/1.94  Demodulation         : 0.30
% 4.67/1.94  BG Simplification    : 0.03
% 4.67/1.94  Subsumption          : 0.13
% 4.67/1.94  Abstraction          : 0.05
% 4.67/1.94  MUC search           : 0.00
% 4.67/1.94  Cooper               : 0.00
% 4.67/1.95  Total                : 1.19
% 4.67/1.95  Index Insertion      : 0.00
% 4.67/1.95  Index Deletion       : 0.00
% 4.67/1.95  Index Matching       : 0.00
% 4.67/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
