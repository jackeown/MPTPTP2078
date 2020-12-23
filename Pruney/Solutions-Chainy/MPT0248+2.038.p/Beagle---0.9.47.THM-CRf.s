%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:09 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 176 expanded)
%              Number of equality atoms :   45 ( 161 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
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

tff(c_20,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_212,plain,(
    ! [B_25,A_26] :
      ( k1_tarski(B_25) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_43,c_212])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_35,c_222])).

tff(c_234,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_235,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_236,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_4])).

tff(c_266,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_295,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_24])).

tff(c_327,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_295])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_327])).

tff(c_330,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_331,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_22,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_437,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_331,c_22])).

tff(c_364,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_343,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_24])).

tff(c_379,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_343])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_432,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_6])).

tff(c_522,plain,(
    ! [B_44,A_45] :
      ( k1_tarski(B_44) = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,k1_tarski(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_533,plain,(
    ! [A_45] :
      ( k1_tarski('#skF_1') = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_522])).

tff(c_539,plain,(
    ! [A_46] :
      ( A_46 = '#skF_2'
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_533])).

tff(c_546,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_432,c_539])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_330,c_437,c_546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  
% 2.07/1.26  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.07/1.26  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.26  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.07/1.26  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.07/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.26  tff(c_20, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.26  tff(c_49, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 2.07/1.26  tff(c_18, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.26  tff(c_35, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_18])).
% 2.07/1.26  tff(c_24, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.26  tff(c_40, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.26  tff(c_43, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_40])).
% 2.07/1.26  tff(c_212, plain, (![B_25, A_26]: (k1_tarski(B_25)=A_26 | k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.26  tff(c_222, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_43, c_212])).
% 2.07/1.26  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_35, c_222])).
% 2.07/1.26  tff(c_234, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 2.07/1.26  tff(c_235, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 2.07/1.26  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.26  tff(c_236, plain, (![A_3]: (k2_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_235, c_4])).
% 2.07/1.26  tff(c_266, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.26  tff(c_295, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_24])).
% 2.07/1.26  tff(c_327, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_295])).
% 2.07/1.26  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_327])).
% 2.07/1.26  tff(c_330, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 2.07/1.26  tff(c_331, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 2.07/1.26  tff(c_22, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.26  tff(c_437, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_331, c_22])).
% 2.07/1.26  tff(c_364, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.26  tff(c_343, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_331, c_24])).
% 2.07/1.26  tff(c_379, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_364, c_343])).
% 2.07/1.26  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.26  tff(c_432, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_379, c_6])).
% 2.07/1.26  tff(c_522, plain, (![B_44, A_45]: (k1_tarski(B_44)=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, k1_tarski(B_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.26  tff(c_533, plain, (![A_45]: (k1_tarski('#skF_1')=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_331, c_522])).
% 2.07/1.26  tff(c_539, plain, (![A_46]: (A_46='#skF_2' | k1_xboole_0=A_46 | ~r1_tarski(A_46, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_533])).
% 2.07/1.26  tff(c_546, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_432, c_539])).
% 2.07/1.26  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_330, c_437, c_546])).
% 2.07/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  Inference rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Ref     : 0
% 2.07/1.26  #Sup     : 128
% 2.07/1.26  #Fact    : 0
% 2.07/1.26  #Define  : 0
% 2.07/1.26  #Split   : 3
% 2.07/1.26  #Chain   : 0
% 2.07/1.26  #Close   : 0
% 2.07/1.26  
% 2.07/1.26  Ordering : KBO
% 2.07/1.26  
% 2.07/1.26  Simplification rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Subsume      : 2
% 2.07/1.26  #Demod        : 48
% 2.07/1.26  #Tautology    : 98
% 2.07/1.26  #SimpNegUnit  : 4
% 2.07/1.26  #BackRed      : 2
% 2.07/1.26  
% 2.07/1.26  #Partial instantiations: 0
% 2.07/1.26  #Strategies tried      : 1
% 2.07/1.26  
% 2.07/1.26  Timing (in seconds)
% 2.07/1.26  ----------------------
% 2.07/1.26  Preprocessing        : 0.28
% 2.07/1.26  Parsing              : 0.14
% 2.07/1.26  CNF conversion       : 0.02
% 2.07/1.26  Main loop            : 0.22
% 2.07/1.26  Inferencing          : 0.08
% 2.07/1.26  Reduction            : 0.08
% 2.07/1.26  Demodulation         : 0.06
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.03
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.52
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
