%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 176 expanded)
%              Number of equality atoms :   45 ( 161 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_39,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8])).

tff(c_322,plain,(
    ! [B_32,A_33] :
      ( k1_tarski(B_32) = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_332,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_58,c_322])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_39,c_332])).

tff(c_346,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_347,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_348,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_4])).

tff(c_402,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_423,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_28])).

tff(c_469,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_423])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_469])).

tff(c_472,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_473,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_532,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_473,c_26])).

tff(c_533,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,A_49) = k2_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_480,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_28])).

tff(c_560,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_480])).

tff(c_610,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_8])).

tff(c_831,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(B_62) = A_63
      | k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_tarski(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_842,plain,(
    ! [A_63] :
      ( k1_tarski('#skF_1') = A_63
      | k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_831])).

tff(c_852,plain,(
    ! [A_64] :
      ( A_64 = '#skF_2'
      | k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_842])).

tff(c_859,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_610,c_852])).

tff(c_871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_532,c_859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:44:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.38  
% 2.49/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.39  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.39  
% 2.49/1.39  %Foreground sorts:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Background operators:
% 2.49/1.39  
% 2.49/1.39  
% 2.49/1.39  %Foreground operators:
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.39  
% 2.49/1.40  tff(f_65, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.49/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.49/1.40  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.49/1.40  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.49/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.49/1.40  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.40  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.40  tff(c_39, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.49/1.40  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.40  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.40  tff(c_58, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8])).
% 2.49/1.40  tff(c_322, plain, (![B_32, A_33]: (k1_tarski(B_32)=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.40  tff(c_332, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_58, c_322])).
% 2.49/1.40  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_39, c_332])).
% 2.49/1.40  tff(c_346, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_347, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.40  tff(c_348, plain, (![A_3]: (k2_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_347, c_4])).
% 2.49/1.40  tff(c_402, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.40  tff(c_423, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_402, c_28])).
% 2.49/1.40  tff(c_469, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_423])).
% 2.49/1.40  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_469])).
% 2.49/1.40  tff(c_472, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.49/1.40  tff(c_473, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.49/1.40  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.49/1.40  tff(c_532, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_473, c_26])).
% 2.49/1.40  tff(c_533, plain, (![B_48, A_49]: (k2_xboole_0(B_48, A_49)=k2_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.40  tff(c_480, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_28])).
% 2.49/1.40  tff(c_560, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_533, c_480])).
% 2.49/1.40  tff(c_610, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_560, c_8])).
% 2.49/1.40  tff(c_831, plain, (![B_62, A_63]: (k1_tarski(B_62)=A_63 | k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.40  tff(c_842, plain, (![A_63]: (k1_tarski('#skF_1')=A_63 | k1_xboole_0=A_63 | ~r1_tarski(A_63, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_831])).
% 2.49/1.40  tff(c_852, plain, (![A_64]: (A_64='#skF_2' | k1_xboole_0=A_64 | ~r1_tarski(A_64, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_842])).
% 2.49/1.40  tff(c_859, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_610, c_852])).
% 2.49/1.40  tff(c_871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_532, c_859])).
% 2.49/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  
% 2.49/1.40  Inference rules
% 2.49/1.40  ----------------------
% 2.49/1.40  #Ref     : 0
% 2.49/1.40  #Sup     : 212
% 2.49/1.40  #Fact    : 0
% 2.49/1.40  #Define  : 0
% 2.49/1.40  #Split   : 3
% 2.49/1.40  #Chain   : 0
% 2.49/1.40  #Close   : 0
% 2.49/1.40  
% 2.49/1.40  Ordering : KBO
% 2.49/1.40  
% 2.49/1.40  Simplification rules
% 2.49/1.40  ----------------------
% 2.49/1.40  #Subsume      : 2
% 2.49/1.40  #Demod        : 73
% 2.49/1.40  #Tautology    : 168
% 2.49/1.40  #SimpNegUnit  : 11
% 2.49/1.40  #BackRed      : 2
% 2.49/1.40  
% 2.49/1.40  #Partial instantiations: 0
% 2.49/1.40  #Strategies tried      : 1
% 2.49/1.40  
% 2.49/1.40  Timing (in seconds)
% 2.49/1.40  ----------------------
% 2.49/1.40  Preprocessing        : 0.31
% 2.49/1.40  Parsing              : 0.16
% 2.49/1.40  CNF conversion       : 0.02
% 2.49/1.40  Main loop            : 0.29
% 2.49/1.40  Inferencing          : 0.11
% 2.49/1.40  Reduction            : 0.10
% 2.49/1.40  Demodulation         : 0.07
% 2.49/1.40  BG Simplification    : 0.02
% 2.49/1.40  Subsumption          : 0.04
% 2.49/1.40  Abstraction          : 0.01
% 2.49/1.40  MUC search           : 0.00
% 2.49/1.40  Cooper               : 0.00
% 2.49/1.40  Total                : 0.63
% 2.49/1.40  Index Insertion      : 0.00
% 2.49/1.40  Index Deletion       : 0.00
% 2.49/1.40  Index Matching       : 0.00
% 2.49/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
