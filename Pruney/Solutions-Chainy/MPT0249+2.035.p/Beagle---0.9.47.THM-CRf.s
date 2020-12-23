%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   44 (  98 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 175 expanded)
%              Number of equality atoms :   30 (  87 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(k2_xboole_0(A_23,B_25),C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_85,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_78])).

tff(c_395,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_401,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_85,c_395])).

tff(c_412,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_401])).

tff(c_137,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_137])).

tff(c_168,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_421,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_168])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_421])).

tff(c_433,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_439,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_30])).

tff(c_492,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,k2_xboole_0(C_59,B_60))
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_504,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_2')
      | ~ r1_tarski(A_58,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_492])).

tff(c_623,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_626,plain,(
    ! [A_74] :
      ( k1_tarski('#skF_1') = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_623])).

tff(c_640,plain,(
    ! [A_75] :
      ( A_75 = '#skF_2'
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_626])).

tff(c_669,plain,(
    ! [A_77] :
      ( A_77 = '#skF_2'
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_504,c_640])).

tff(c_673,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_669])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_28,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.38  
% 2.57/1.38  %Foreground sorts:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Background operators:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Foreground operators:
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.38  
% 2.57/1.39  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.57/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.39  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.57/1.39  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.57/1.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.57/1.39  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.39  tff(c_28, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.39  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.39  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.39  tff(c_69, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(k2_xboole_0(A_23, B_25), C_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.39  tff(c_78, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.57/1.39  tff(c_85, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_78])).
% 2.57/1.39  tff(c_395, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.39  tff(c_401, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_85, c_395])).
% 2.57/1.39  tff(c_412, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_26, c_401])).
% 2.57/1.39  tff(c_137, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.39  tff(c_149, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_85, c_137])).
% 2.57/1.39  tff(c_168, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_149])).
% 2.57/1.39  tff(c_421, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_412, c_168])).
% 2.57/1.39  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_421])).
% 2.57/1.39  tff(c_433, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_149])).
% 2.57/1.39  tff(c_439, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_30])).
% 2.57/1.39  tff(c_492, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, k2_xboole_0(C_59, B_60)) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.39  tff(c_504, plain, (![A_58]: (r1_tarski(A_58, '#skF_2') | ~r1_tarski(A_58, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_492])).
% 2.57/1.39  tff(c_623, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.39  tff(c_626, plain, (![A_74]: (k1_tarski('#skF_1')=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_433, c_623])).
% 2.57/1.39  tff(c_640, plain, (![A_75]: (A_75='#skF_2' | k1_xboole_0=A_75 | ~r1_tarski(A_75, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_626])).
% 2.57/1.39  tff(c_669, plain, (![A_77]: (A_77='#skF_2' | k1_xboole_0=A_77 | ~r1_tarski(A_77, '#skF_3'))), inference(resolution, [status(thm)], [c_504, c_640])).
% 2.57/1.39  tff(c_673, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_669])).
% 2.57/1.39  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_28, c_673])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 144
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 1
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 3
% 2.57/1.39  #Demod        : 55
% 2.57/1.39  #Tautology    : 62
% 2.57/1.39  #SimpNegUnit  : 6
% 2.57/1.39  #BackRed      : 13
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.39  Preprocessing        : 0.29
% 2.57/1.39  Parsing              : 0.16
% 2.57/1.39  CNF conversion       : 0.02
% 2.57/1.39  Main loop            : 0.33
% 2.57/1.39  Inferencing          : 0.11
% 2.57/1.39  Reduction            : 0.11
% 2.57/1.39  Demodulation         : 0.08
% 2.57/1.39  BG Simplification    : 0.02
% 2.57/1.39  Subsumption          : 0.07
% 2.57/1.39  Abstraction          : 0.01
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.39  Total                : 0.65
% 2.57/1.39  Index Insertion      : 0.00
% 2.57/1.39  Index Deletion       : 0.00
% 2.57/1.39  Index Matching       : 0.00
% 2.57/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
