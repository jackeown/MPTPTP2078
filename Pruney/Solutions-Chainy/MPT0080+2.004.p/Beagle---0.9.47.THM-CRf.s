%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 134 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_176,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_184,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_176,c_24])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_146,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_131])).

tff(c_302,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_363,plain,(
    ! [A_7,C_50] : k4_xboole_0(A_7,k2_xboole_0(A_7,C_50)) = k4_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_302])).

tff(c_374,plain,(
    ! [C_50] : k4_xboole_0(k1_xboole_0,C_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_363])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_213,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_221,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_213])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_481,plain,(
    ! [A_53,B_54] :
      ( k2_xboole_0(A_53,B_54) = B_54
      | k4_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_513,plain,(
    ! [C_55] : k2_xboole_0(k1_xboole_0,C_55) = C_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_481])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_528,plain,(
    ! [C_55] : k2_xboole_0(C_55,k1_xboole_0) = C_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_2])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_145,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_131])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_315,plain,(
    ! [A_48,B_49,B_17] : k4_xboole_0(A_48,k2_xboole_0(B_49,k4_xboole_0(k4_xboole_0(A_48,B_49),B_17))) = k3_xboole_0(k4_xboole_0(A_48,B_49),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_20])).

tff(c_3331,plain,(
    ! [A_109,B_110,B_111] : k4_xboole_0(A_109,k2_xboole_0(B_110,k4_xboole_0(A_109,k2_xboole_0(B_110,B_111)))) = k3_xboole_0(k4_xboole_0(A_109,B_110),B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_315])).

tff(c_3502,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_3331])).

tff(c_3556,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_4,c_3502])).

tff(c_2140,plain,(
    ! [A_87,B_88,C_89] : k4_xboole_0(A_87,k2_xboole_0(k4_xboole_0(A_87,B_88),C_89)) = k4_xboole_0(k3_xboole_0(A_87,B_88),C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_302])).

tff(c_44,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_25,B_24] : r1_tarski(A_25,k2_xboole_0(B_24,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_144,plain,(
    ! [A_25,B_24] : k4_xboole_0(A_25,k2_xboole_0(B_24,A_25)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_131])).

tff(c_2307,plain,(
    ! [C_90,B_91] : k4_xboole_0(k3_xboole_0(C_90,B_91),C_90) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2140,c_144])).

tff(c_243,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_2365,plain,(
    ! [C_90,B_91] : k2_xboole_0(k3_xboole_0(C_90,B_91),C_90) = C_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_2307,c_243])).

tff(c_4030,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3556,c_2365])).

tff(c_339,plain,(
    ! [A_16,B_17,C_50] : k4_xboole_0(A_16,k2_xboole_0(k4_xboole_0(A_16,B_17),C_50)) = k4_xboole_0(k3_xboole_0(A_16,B_17),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_302])).

tff(c_4872,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4030,c_339])).

tff(c_4937,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_221,c_4872])).

tff(c_4939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_4937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.96  
% 4.66/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.97  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.66/1.97  
% 4.66/1.97  %Foreground sorts:
% 4.66/1.97  
% 4.66/1.97  
% 4.66/1.97  %Background operators:
% 4.66/1.97  
% 4.66/1.97  
% 4.66/1.97  %Foreground operators:
% 4.66/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.66/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.66/1.97  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.97  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/1.97  
% 4.66/1.98  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.66/1.98  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.66/1.98  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.66/1.98  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.66/1.98  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.66/1.98  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.66/1.98  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.66/1.98  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.66/1.98  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.66/1.98  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/1.98  tff(c_176, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.98  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.98  tff(c_184, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_176, c_24])).
% 4.66/1.98  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.66/1.98  tff(c_131, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.98  tff(c_147, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_131])).
% 4.66/1.98  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.66/1.98  tff(c_39, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.66/1.98  tff(c_42, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_39])).
% 4.66/1.98  tff(c_146, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_131])).
% 4.66/1.98  tff(c_302, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.98  tff(c_363, plain, (![A_7, C_50]: (k4_xboole_0(A_7, k2_xboole_0(A_7, C_50))=k4_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_146, c_302])).
% 4.66/1.98  tff(c_374, plain, (![C_50]: (k4_xboole_0(k1_xboole_0, C_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_363])).
% 4.66/1.98  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.98  tff(c_213, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.66/1.98  tff(c_221, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_213])).
% 4.66/1.98  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.66/1.98  tff(c_227, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.66/1.98  tff(c_481, plain, (![A_53, B_54]: (k2_xboole_0(A_53, B_54)=B_54 | k4_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_227])).
% 4.66/1.98  tff(c_513, plain, (![C_55]: (k2_xboole_0(k1_xboole_0, C_55)=C_55)), inference(superposition, [status(thm), theory('equality')], [c_374, c_481])).
% 4.66/1.98  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.98  tff(c_528, plain, (![C_55]: (k2_xboole_0(C_55, k1_xboole_0)=C_55)), inference(superposition, [status(thm), theory('equality')], [c_513, c_2])).
% 4.66/1.98  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.98  tff(c_28, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.98  tff(c_29, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 4.66/1.98  tff(c_145, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_131])).
% 4.66/1.98  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.98  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.66/1.98  tff(c_315, plain, (![A_48, B_49, B_17]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k4_xboole_0(k4_xboole_0(A_48, B_49), B_17)))=k3_xboole_0(k4_xboole_0(A_48, B_49), B_17))), inference(superposition, [status(thm), theory('equality')], [c_302, c_20])).
% 4.66/1.98  tff(c_3331, plain, (![A_109, B_110, B_111]: (k4_xboole_0(A_109, k2_xboole_0(B_110, k4_xboole_0(A_109, k2_xboole_0(B_110, B_111))))=k3_xboole_0(k4_xboole_0(A_109, B_110), B_111))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_315])).
% 4.66/1.98  tff(c_3502, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_3331])).
% 4.66/1.98  tff(c_3556, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_528, c_4, c_3502])).
% 4.66/1.98  tff(c_2140, plain, (![A_87, B_88, C_89]: (k4_xboole_0(A_87, k2_xboole_0(k4_xboole_0(A_87, B_88), C_89))=k4_xboole_0(k3_xboole_0(A_87, B_88), C_89))), inference(superposition, [status(thm), theory('equality')], [c_20, c_302])).
% 4.66/1.98  tff(c_44, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.98  tff(c_59, plain, (![A_25, B_24]: (r1_tarski(A_25, k2_xboole_0(B_24, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_22])).
% 4.66/1.98  tff(c_144, plain, (![A_25, B_24]: (k4_xboole_0(A_25, k2_xboole_0(B_24, A_25))=k1_xboole_0)), inference(resolution, [status(thm)], [c_59, c_131])).
% 4.66/1.98  tff(c_2307, plain, (![C_90, B_91]: (k4_xboole_0(k3_xboole_0(C_90, B_91), C_90)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2140, c_144])).
% 4.66/1.98  tff(c_243, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_227])).
% 4.66/1.98  tff(c_2365, plain, (![C_90, B_91]: (k2_xboole_0(k3_xboole_0(C_90, B_91), C_90)=C_90)), inference(superposition, [status(thm), theory('equality')], [c_2307, c_243])).
% 4.66/1.98  tff(c_4030, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3556, c_2365])).
% 4.66/1.98  tff(c_339, plain, (![A_16, B_17, C_50]: (k4_xboole_0(A_16, k2_xboole_0(k4_xboole_0(A_16, B_17), C_50))=k4_xboole_0(k3_xboole_0(A_16, B_17), C_50))), inference(superposition, [status(thm), theory('equality')], [c_20, c_302])).
% 4.66/1.98  tff(c_4872, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4030, c_339])).
% 4.66/1.98  tff(c_4937, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_374, c_221, c_4872])).
% 4.66/1.98  tff(c_4939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_4937])).
% 4.66/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.98  
% 4.66/1.98  Inference rules
% 4.66/1.98  ----------------------
% 4.66/1.98  #Ref     : 0
% 4.66/1.98  #Sup     : 1221
% 4.66/1.98  #Fact    : 0
% 4.66/1.98  #Define  : 0
% 4.66/1.98  #Split   : 0
% 4.66/1.98  #Chain   : 0
% 4.66/1.98  #Close   : 0
% 4.66/1.98  
% 4.66/1.98  Ordering : KBO
% 4.66/1.98  
% 4.66/1.98  Simplification rules
% 4.66/1.98  ----------------------
% 4.66/1.98  #Subsume      : 24
% 4.66/1.98  #Demod        : 1277
% 4.66/1.98  #Tautology    : 801
% 4.66/1.98  #SimpNegUnit  : 1
% 4.66/1.98  #BackRed      : 0
% 4.66/1.98  
% 4.66/1.98  #Partial instantiations: 0
% 4.66/1.98  #Strategies tried      : 1
% 4.66/1.98  
% 4.66/1.98  Timing (in seconds)
% 4.66/1.98  ----------------------
% 4.97/1.98  Preprocessing        : 0.29
% 4.97/1.98  Parsing              : 0.16
% 4.97/1.98  CNF conversion       : 0.02
% 4.97/1.98  Main loop            : 0.88
% 4.97/1.98  Inferencing          : 0.26
% 4.97/1.98  Reduction            : 0.43
% 4.97/1.98  Demodulation         : 0.37
% 4.97/1.98  BG Simplification    : 0.03
% 4.97/1.98  Subsumption          : 0.11
% 4.97/1.98  Abstraction          : 0.04
% 4.97/1.98  MUC search           : 0.00
% 4.97/1.98  Cooper               : 0.00
% 4.97/1.98  Total                : 1.20
% 4.97/1.98  Index Insertion      : 0.00
% 4.97/1.98  Index Deletion       : 0.00
% 4.97/1.98  Index Matching       : 0.00
% 4.97/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
