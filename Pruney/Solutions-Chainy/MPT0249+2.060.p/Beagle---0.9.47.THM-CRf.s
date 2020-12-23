%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   45 (  88 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 139 expanded)
%              Number of equality atoms :   27 ( 103 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ! [A_42,B_43] : r1_tarski(A_42,k2_xboole_0(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_110,plain,(
    ! [B_56,A_57] :
      ( k1_tarski(B_56) = A_57
      | k1_xboole_0 = A_57
      | ~ r1_tarski(A_57,k1_tarski(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_45,c_110])).

tff(c_128,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_119])).

tff(c_133,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_36])).

tff(c_221,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k2_xboole_0(A_67,B_68),C_69) = k2_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_261,plain,(
    ! [C_70] : k2_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_70)) = k2_xboole_0('#skF_2',C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_221])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_881,plain,(
    ! [A_118,C_119] :
      ( r1_tarski(A_118,k2_xboole_0('#skF_2',C_119))
      | ~ r1_tarski(A_118,k2_xboole_0('#skF_3',C_119)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_2])).

tff(c_909,plain,(
    ! [A_121] :
      ( r1_tarski(A_121,'#skF_2')
      | ~ r1_tarski(A_121,k2_xboole_0('#skF_3','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_881])).

tff(c_919,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_909])).

tff(c_22,plain,(
    ! [B_38,A_37] :
      ( k1_tarski(B_38) = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_37] :
      ( k1_tarski('#skF_1') = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_22])).

tff(c_154,plain,(
    ! [A_37] :
      ( A_37 = '#skF_2'
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_137])).

tff(c_922,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_919,c_154])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_34,c_922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.97  
% 3.74/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.97  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.74/1.97  
% 3.74/1.97  %Foreground sorts:
% 3.74/1.97  
% 3.74/1.97  
% 3.74/1.97  %Background operators:
% 3.74/1.97  
% 3.74/1.97  
% 3.74/1.97  %Foreground operators:
% 3.74/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.97  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.97  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.97  tff('#skF_1', type, '#skF_1': $i).
% 3.74/1.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.97  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.74/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.74/1.97  
% 3.99/1.99  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.99/1.99  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.99/1.99  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.99/1.99  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.99/1.99  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.99/1.99  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.99  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.99  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.99  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.99  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.99  tff(c_42, plain, (![A_42, B_43]: (r1_tarski(A_42, k2_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.99/1.99  tff(c_45, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_42])).
% 3.99/1.99  tff(c_110, plain, (![B_56, A_57]: (k1_tarski(B_56)=A_57 | k1_xboole_0=A_57 | ~r1_tarski(A_57, k1_tarski(B_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.99  tff(c_119, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_45, c_110])).
% 3.99/1.99  tff(c_128, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_119])).
% 3.99/1.99  tff(c_133, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_36])).
% 3.99/1.99  tff(c_221, plain, (![A_67, B_68, C_69]: (k2_xboole_0(k2_xboole_0(A_67, B_68), C_69)=k2_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.99  tff(c_261, plain, (![C_70]: (k2_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_70))=k2_xboole_0('#skF_2', C_70))), inference(superposition, [status(thm), theory('equality')], [c_133, c_221])).
% 3.99/1.99  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.99  tff(c_881, plain, (![A_118, C_119]: (r1_tarski(A_118, k2_xboole_0('#skF_2', C_119)) | ~r1_tarski(A_118, k2_xboole_0('#skF_3', C_119)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_2])).
% 3.99/1.99  tff(c_909, plain, (![A_121]: (r1_tarski(A_121, '#skF_2') | ~r1_tarski(A_121, k2_xboole_0('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_133, c_881])).
% 3.99/1.99  tff(c_919, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_909])).
% 3.99/1.99  tff(c_22, plain, (![B_38, A_37]: (k1_tarski(B_38)=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.99  tff(c_137, plain, (![A_37]: (k1_tarski('#skF_1')=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_22])).
% 3.99/1.99  tff(c_154, plain, (![A_37]: (A_37='#skF_2' | k1_xboole_0=A_37 | ~r1_tarski(A_37, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_137])).
% 3.99/1.99  tff(c_922, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_919, c_154])).
% 3.99/1.99  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_34, c_922])).
% 3.99/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.99  
% 3.99/1.99  Inference rules
% 3.99/1.99  ----------------------
% 3.99/1.99  #Ref     : 0
% 3.99/1.99  #Sup     : 224
% 3.99/1.99  #Fact    : 0
% 3.99/1.99  #Define  : 0
% 3.99/1.99  #Split   : 0
% 3.99/1.99  #Chain   : 0
% 3.99/1.99  #Close   : 0
% 3.99/1.99  
% 3.99/1.99  Ordering : KBO
% 3.99/1.99  
% 3.99/1.99  Simplification rules
% 3.99/1.99  ----------------------
% 3.99/1.99  #Subsume      : 12
% 3.99/1.99  #Demod        : 100
% 3.99/1.99  #Tautology    : 80
% 3.99/1.99  #SimpNegUnit  : 4
% 3.99/1.99  #BackRed      : 3
% 3.99/1.99  
% 3.99/1.99  #Partial instantiations: 0
% 3.99/1.99  #Strategies tried      : 1
% 3.99/1.99  
% 3.99/1.99  Timing (in seconds)
% 3.99/1.99  ----------------------
% 3.99/1.99  Preprocessing        : 0.51
% 3.99/1.99  Parsing              : 0.27
% 3.99/1.99  CNF conversion       : 0.03
% 3.99/1.99  Main loop            : 0.62
% 3.99/1.99  Inferencing          : 0.22
% 3.99/1.99  Reduction            : 0.24
% 3.99/1.99  Demodulation         : 0.19
% 3.99/2.00  BG Simplification    : 0.03
% 3.99/2.00  Subsumption          : 0.10
% 3.99/2.00  Abstraction          : 0.03
% 3.99/2.00  MUC search           : 0.00
% 3.99/2.00  Cooper               : 0.00
% 3.99/2.00  Total                : 1.18
% 3.99/2.00  Index Insertion      : 0.00
% 3.99/2.00  Index Deletion       : 0.00
% 3.99/2.00  Index Matching       : 0.00
% 3.99/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
