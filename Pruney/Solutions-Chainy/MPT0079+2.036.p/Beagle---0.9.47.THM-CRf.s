%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:47 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 232 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :   91 ( 281 expanded)
%              Number of equality atoms :   64 ( 221 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_887,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k4_xboole_0(A_64,B_65),C_66) = k4_xboole_0(A_64,k2_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_237,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_222])).

tff(c_240,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_237])).

tff(c_903,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(B_65,k4_xboole_0(A_64,B_65))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_240])).

tff(c_969,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_903])).

tff(c_999,plain,(
    ! [A_20,B_21] : k4_xboole_0(k4_xboole_0(A_20,B_21),A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_969])).

tff(c_71,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_32] : k2_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_987,plain,(
    ! [A_67,B_68] : k3_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = k4_xboole_0(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_20])).

tff(c_1024,plain,(
    ! [A_67,B_68] : k3_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_987])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_449,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_xboole_0(A_51,B_52)
      | ~ r1_xboole_0(A_51,k2_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2446,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_xboole_0(A_113,B_114)
      | k3_xboole_0(A_113,k2_xboole_0(B_114,C_115)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_449])).

tff(c_2506,plain,(
    ! [A_116,B_117] :
      ( r1_xboole_0(A_116,B_117)
      | k1_xboole_0 != A_116 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_2446])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2554,plain,(
    ! [B_118,A_119] :
      ( r1_xboole_0(B_118,A_119)
      | k1_xboole_0 != A_119 ) ),
    inference(resolution,[status(thm)],[c_2506,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2745,plain,(
    ! [B_123,A_124] :
      ( k3_xboole_0(B_123,A_124) = k1_xboole_0
      | k1_xboole_0 != A_124 ) ),
    inference(resolution,[status(thm)],[c_2554,c_4])).

tff(c_2790,plain,(
    ! [B_123,A_124] :
      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(B_123,A_124)) = B_123
      | k1_xboole_0 != A_124 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2745,c_24])).

tff(c_3414,plain,(
    ! [B_139,A_140] :
      ( k4_xboole_0(B_139,A_140) = B_139
      | k1_xboole_0 != A_140 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_2790])).

tff(c_3588,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,B_143) = k1_xboole_0
      | k1_xboole_0 != A_142 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_3414])).

tff(c_3654,plain,(
    ! [B_143,A_142] :
      ( k2_xboole_0(B_143,k1_xboole_0) = k2_xboole_0(B_143,A_142)
      | k1_xboole_0 != A_142 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3588,c_14])).

tff(c_3808,plain,(
    ! [B_143] : k2_xboole_0(B_143,k1_xboole_0) = B_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3654])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_177,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_195,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_177])).

tff(c_341,plain,(
    ! [A_49,B_50] : k2_xboole_0(k3_xboole_0(A_49,B_50),k4_xboole_0(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_362,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_341])).

tff(c_812,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_87])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_41,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_1017,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_969])).

tff(c_14074,plain,(
    ! [C_244,A_245,B_246] : k2_xboole_0(C_244,k4_xboole_0(A_245,k2_xboole_0(B_246,C_244))) = k2_xboole_0(C_244,k4_xboole_0(A_245,B_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_887,c_14])).

tff(c_14380,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_14074])).

tff(c_14481,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3808,c_812,c_14380])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_197,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_365,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_341])).

tff(c_384,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_87])).

tff(c_959,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(B_65,A_64)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_903])).

tff(c_15733,plain,(
    ! [A_252] : k2_xboole_0('#skF_2',k4_xboole_0(A_252,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_252,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_14074])).

tff(c_15933,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_15733])).

tff(c_15976,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3808,c_14481,c_2,c_384,c_15933])).

tff(c_15978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_15976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.98  
% 9.86/3.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.98  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.86/3.98  
% 9.86/3.98  %Foreground sorts:
% 9.86/3.98  
% 9.86/3.98  
% 9.86/3.98  %Background operators:
% 9.86/3.98  
% 9.86/3.98  
% 9.86/3.98  %Foreground operators:
% 9.86/3.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.86/3.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.86/3.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.86/3.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.86/3.98  tff('#skF_2', type, '#skF_2': $i).
% 9.86/3.98  tff('#skF_3', type, '#skF_3': $i).
% 9.86/3.98  tff('#skF_1', type, '#skF_1': $i).
% 9.86/3.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.86/3.98  tff('#skF_4', type, '#skF_4': $i).
% 9.86/3.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.86/3.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.86/3.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.86/3.98  
% 9.86/3.99  tff(f_84, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.86/3.99  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.86/3.99  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.86/3.99  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 9.86/3.99  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.86/3.99  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.86/3.99  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.86/3.99  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.86/3.99  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.86/3.99  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.86/3.99  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 9.86/3.99  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.86/3.99  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.86/3.99  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.86/3.99  tff(c_24, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.86/3.99  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.86/3.99  tff(c_887, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k4_xboole_0(A_64, B_65), C_66)=k4_xboole_0(A_64, k2_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.86/3.99  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.86/3.99  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.86/3.99  tff(c_222, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.86/3.99  tff(c_237, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_222])).
% 9.86/3.99  tff(c_240, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_237])).
% 9.86/3.99  tff(c_903, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(B_65, k4_xboole_0(A_64, B_65)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_887, c_240])).
% 9.86/3.99  tff(c_969, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k2_xboole_0(B_68, A_67))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_903])).
% 9.86/3.99  tff(c_999, plain, (![A_20, B_21]: (k4_xboole_0(k4_xboole_0(A_20, B_21), A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_969])).
% 9.86/3.99  tff(c_71, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.86/3.99  tff(c_87, plain, (![A_32]: (k2_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_71, c_10])).
% 9.86/3.99  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.86/3.99  tff(c_987, plain, (![A_67, B_68]: (k3_xboole_0(A_67, k2_xboole_0(B_68, A_67))=k4_xboole_0(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_969, c_20])).
% 9.86/3.99  tff(c_1024, plain, (![A_67, B_68]: (k3_xboole_0(A_67, k2_xboole_0(B_68, A_67))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_987])).
% 9.86/3.99  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.86/3.99  tff(c_449, plain, (![A_51, B_52, C_53]: (r1_xboole_0(A_51, B_52) | ~r1_xboole_0(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.86/3.99  tff(c_2446, plain, (![A_113, B_114, C_115]: (r1_xboole_0(A_113, B_114) | k3_xboole_0(A_113, k2_xboole_0(B_114, C_115))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_449])).
% 9.86/3.99  tff(c_2506, plain, (![A_116, B_117]: (r1_xboole_0(A_116, B_117) | k1_xboole_0!=A_116)), inference(superposition, [status(thm), theory('equality')], [c_1024, c_2446])).
% 9.86/3.99  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.99  tff(c_2554, plain, (![B_118, A_119]: (r1_xboole_0(B_118, A_119) | k1_xboole_0!=A_119)), inference(resolution, [status(thm)], [c_2506, c_8])).
% 9.86/3.99  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.86/3.99  tff(c_2745, plain, (![B_123, A_124]: (k3_xboole_0(B_123, A_124)=k1_xboole_0 | k1_xboole_0!=A_124)), inference(resolution, [status(thm)], [c_2554, c_4])).
% 9.86/3.99  tff(c_2790, plain, (![B_123, A_124]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(B_123, A_124))=B_123 | k1_xboole_0!=A_124)), inference(superposition, [status(thm), theory('equality')], [c_2745, c_24])).
% 9.86/3.99  tff(c_3414, plain, (![B_139, A_140]: (k4_xboole_0(B_139, A_140)=B_139 | k1_xboole_0!=A_140)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_2790])).
% 9.86/3.99  tff(c_3588, plain, (![A_142, B_143]: (k4_xboole_0(A_142, B_143)=k1_xboole_0 | k1_xboole_0!=A_142)), inference(superposition, [status(thm), theory('equality')], [c_999, c_3414])).
% 9.86/3.99  tff(c_3654, plain, (![B_143, A_142]: (k2_xboole_0(B_143, k1_xboole_0)=k2_xboole_0(B_143, A_142) | k1_xboole_0!=A_142)), inference(superposition, [status(thm), theory('equality')], [c_3588, c_14])).
% 9.86/3.99  tff(c_3808, plain, (![B_143]: (k2_xboole_0(B_143, k1_xboole_0)=B_143)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3654])).
% 9.86/3.99  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.86/3.99  tff(c_155, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.99  tff(c_160, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_155])).
% 9.86/3.99  tff(c_177, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.86/3.99  tff(c_195, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_177])).
% 9.86/3.99  tff(c_341, plain, (![A_49, B_50]: (k2_xboole_0(k3_xboole_0(A_49, B_50), k4_xboole_0(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.86/3.99  tff(c_362, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_195, c_341])).
% 9.86/3.99  tff(c_812, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_362, c_87])).
% 9.86/3.99  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.86/3.99  tff(c_40, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.86/3.99  tff(c_41, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 9.86/3.99  tff(c_1017, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_969])).
% 9.86/3.99  tff(c_14074, plain, (![C_244, A_245, B_246]: (k2_xboole_0(C_244, k4_xboole_0(A_245, k2_xboole_0(B_246, C_244)))=k2_xboole_0(C_244, k4_xboole_0(A_245, B_246)))), inference(superposition, [status(thm), theory('equality')], [c_887, c_14])).
% 9.86/3.99  tff(c_14380, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1017, c_14074])).
% 9.86/3.99  tff(c_14481, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3808, c_812, c_14380])).
% 9.86/3.99  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.86/3.99  tff(c_197, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_177])).
% 9.86/3.99  tff(c_365, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_197, c_341])).
% 9.86/3.99  tff(c_384, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_365, c_87])).
% 9.86/3.99  tff(c_959, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(B_65, A_64))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_903])).
% 9.86/3.99  tff(c_15733, plain, (![A_252]: (k2_xboole_0('#skF_2', k4_xboole_0(A_252, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_252, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41, c_14074])).
% 9.86/3.99  tff(c_15933, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_959, c_15733])).
% 9.86/3.99  tff(c_15976, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3808, c_14481, c_2, c_384, c_15933])).
% 9.86/3.99  tff(c_15978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_15976])).
% 9.86/3.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.99  
% 9.86/3.99  Inference rules
% 9.86/3.99  ----------------------
% 9.86/3.99  #Ref     : 2
% 9.86/3.99  #Sup     : 4235
% 9.86/3.99  #Fact    : 0
% 9.86/3.99  #Define  : 0
% 9.86/3.99  #Split   : 5
% 9.86/3.99  #Chain   : 0
% 9.86/3.99  #Close   : 0
% 9.86/3.99  
% 9.86/3.99  Ordering : KBO
% 9.86/3.99  
% 9.86/3.99  Simplification rules
% 9.86/3.99  ----------------------
% 9.86/3.99  #Subsume      : 867
% 9.86/3.99  #Demod        : 3412
% 9.86/3.99  #Tautology    : 1777
% 9.86/3.99  #SimpNegUnit  : 54
% 9.86/3.99  #BackRed      : 14
% 9.86/3.99  
% 9.86/3.99  #Partial instantiations: 0
% 9.86/3.99  #Strategies tried      : 1
% 9.86/3.99  
% 9.86/3.99  Timing (in seconds)
% 9.86/3.99  ----------------------
% 9.86/4.00  Preprocessing        : 0.48
% 9.86/4.00  Parsing              : 0.25
% 9.86/4.00  CNF conversion       : 0.03
% 9.86/4.00  Main loop            : 2.57
% 9.86/4.00  Inferencing          : 0.55
% 9.86/4.00  Reduction            : 1.39
% 9.86/4.00  Demodulation         : 1.20
% 9.86/4.00  BG Simplification    : 0.07
% 9.86/4.00  Subsumption          : 0.42
% 9.86/4.00  Abstraction          : 0.09
% 9.86/4.00  MUC search           : 0.00
% 9.86/4.00  Cooper               : 0.00
% 9.86/4.00  Total                : 3.09
% 9.86/4.00  Index Insertion      : 0.00
% 9.86/4.00  Index Deletion       : 0.00
% 9.86/4.00  Index Matching       : 0.00
% 9.86/4.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
