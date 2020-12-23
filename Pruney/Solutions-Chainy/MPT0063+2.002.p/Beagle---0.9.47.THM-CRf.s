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
% DateTime   : Thu Dec  3 09:43:08 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 102 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_28,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_479,plain,(
    ! [A_46,B_47] :
      ( r2_xboole_0(A_46,B_47)
      | B_47 = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_502,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_479,c_24])).

tff(c_507,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ r2_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_176,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_176])).

tff(c_18,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_253,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_18])).

tff(c_256,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,A_3) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_155,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_147])).

tff(c_200,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155,c_176])).

tff(c_216,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k4_xboole_0(B_38,A_37)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_238,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_216])).

tff(c_248,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_238])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_xboole_0(A_12,B_13),C_14) = k2_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_522,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k2_xboole_0(A_48,B_49),C_50) = k2_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_59,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_622,plain,(
    ! [C_51,A_52,B_53] : r1_tarski(C_51,k2_xboole_0(A_52,k2_xboole_0(B_53,C_51))) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_59])).

tff(c_662,plain,(
    ! [C_51,B_53,A_3] : r1_tarski(C_51,k2_xboole_0(k2_xboole_0(B_53,C_51),A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_622])).

tff(c_1214,plain,(
    ! [C_66,B_67,A_68] : r1_tarski(C_66,k2_xboole_0(B_67,k2_xboole_0(C_66,A_68))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_662])).

tff(c_1293,plain,(
    ! [B_69] : r1_tarski('#skF_1',k2_xboole_0(B_69,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_1214])).

tff(c_1308,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_1293])).

tff(c_1325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_507,c_1308])).

tff(c_1326,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_137,plain,(
    ! [B_25,A_26] :
      ( ~ r2_xboole_0(B_25,A_26)
      | ~ r2_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_142,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_1331,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_142])).

tff(c_1336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  
% 2.72/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.44  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.44  
% 2.72/1.45  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_xboole_1)).
% 2.72/1.45  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.72/1.45  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.72/1.45  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.45  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.72/1.45  tff(f_32, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.72/1.45  tff(f_49, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.72/1.45  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.72/1.45  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 2.72/1.45  tff(c_28, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.45  tff(c_479, plain, (![A_46, B_47]: (r2_xboole_0(A_46, B_47) | B_47=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_24, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.45  tff(c_502, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_479, c_24])).
% 2.72/1.45  tff(c_507, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_502])).
% 2.72/1.45  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.45  tff(c_26, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.72/1.45  tff(c_147, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~r2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_154, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_147])).
% 2.72/1.45  tff(c_176, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.45  tff(c_201, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_176])).
% 2.72/1.45  tff(c_18, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.45  tff(c_253, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_201, c_18])).
% 2.72/1.45  tff(c_256, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_253])).
% 2.72/1.45  tff(c_4, plain, (![B_4, A_3]: (k2_xboole_0(B_4, A_3)=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.45  tff(c_155, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_147])).
% 2.72/1.45  tff(c_200, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_155, c_176])).
% 2.72/1.45  tff(c_216, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k4_xboole_0(B_38, A_37))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.45  tff(c_238, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_200, c_216])).
% 2.72/1.45  tff(c_248, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_238])).
% 2.72/1.45  tff(c_20, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_xboole_0(A_12, B_13), C_14)=k2_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.45  tff(c_522, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k2_xboole_0(A_48, B_49), C_50)=k2_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.45  tff(c_44, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.45  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.45  tff(c_59, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_22])).
% 2.72/1.45  tff(c_622, plain, (![C_51, A_52, B_53]: (r1_tarski(C_51, k2_xboole_0(A_52, k2_xboole_0(B_53, C_51))))), inference(superposition, [status(thm), theory('equality')], [c_522, c_59])).
% 2.72/1.45  tff(c_662, plain, (![C_51, B_53, A_3]: (r1_tarski(C_51, k2_xboole_0(k2_xboole_0(B_53, C_51), A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_622])).
% 2.72/1.45  tff(c_1214, plain, (![C_66, B_67, A_68]: (r1_tarski(C_66, k2_xboole_0(B_67, k2_xboole_0(C_66, A_68))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_662])).
% 2.72/1.45  tff(c_1293, plain, (![B_69]: (r1_tarski('#skF_1', k2_xboole_0(B_69, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_248, c_1214])).
% 2.72/1.45  tff(c_1308, plain, (r1_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_256, c_1293])).
% 2.72/1.45  tff(c_1325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_507, c_1308])).
% 2.72/1.45  tff(c_1326, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_502])).
% 2.72/1.45  tff(c_137, plain, (![B_25, A_26]: (~r2_xboole_0(B_25, A_26) | ~r2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.72/1.45  tff(c_142, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_137])).
% 2.72/1.45  tff(c_1331, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_142])).
% 2.72/1.45  tff(c_1336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1331])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 326
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 3
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 2
% 2.72/1.45  #Demod        : 201
% 2.72/1.45  #Tautology    : 213
% 2.72/1.45  #SimpNegUnit  : 1
% 2.72/1.45  #BackRed      : 6
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.45  Preprocessing        : 0.26
% 2.72/1.45  Parsing              : 0.15
% 2.72/1.45  CNF conversion       : 0.02
% 2.72/1.45  Main loop            : 0.41
% 2.72/1.45  Inferencing          : 0.14
% 2.72/1.45  Reduction            : 0.16
% 2.72/1.45  Demodulation         : 0.13
% 2.72/1.45  BG Simplification    : 0.02
% 2.72/1.46  Subsumption          : 0.07
% 2.72/1.46  Abstraction          : 0.02
% 2.72/1.46  MUC search           : 0.00
% 2.72/1.46  Cooper               : 0.00
% 2.72/1.46  Total                : 0.70
% 2.72/1.46  Index Insertion      : 0.00
% 2.72/1.46  Index Deletion       : 0.00
% 2.72/1.46  Index Matching       : 0.00
% 2.72/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
