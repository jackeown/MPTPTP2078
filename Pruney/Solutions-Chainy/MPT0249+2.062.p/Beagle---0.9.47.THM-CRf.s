%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   30 (  57 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   39 ( 100 expanded)
%              Number of equality atoms :   33 (  84 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_43,plain,(
    ! [B_12,A_13] :
      ( k1_tarski(B_12) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_55,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_61,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_32])).

tff(c_110,plain,(
    ! [A_18,C_19,B_20] :
      ( k1_tarski(A_18) = C_19
      | k1_xboole_0 = C_19
      | k2_xboole_0(B_20,C_19) != k1_tarski(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_18] :
      ( k1_tarski(A_18) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k1_tarski(A_18) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_110])).

tff(c_115,plain,(
    ! [A_21] :
      ( k1_tarski(A_21) = '#skF_3'
      | k1_tarski(A_21) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_113])).

tff(c_119,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_115])).

tff(c_120,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_55])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  
% 1.60/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.17  %$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.60/1.17  
% 1.60/1.17  %Foreground sorts:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Background operators:
% 1.60/1.17  
% 1.60/1.17  
% 1.60/1.17  %Foreground operators:
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.17  
% 1.82/1.18  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.82/1.18  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.82/1.18  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 1.82/1.18  tff(f_51, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 1.82/1.18  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.18  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.18  tff(c_32, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.18  tff(c_39, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.18  tff(c_42, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_39])).
% 1.82/1.18  tff(c_43, plain, (![B_12, A_13]: (k1_tarski(B_12)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_12)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.18  tff(c_46, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_43])).
% 1.82/1.18  tff(c_55, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28, c_46])).
% 1.82/1.18  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.82/1.18  tff(c_61, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_32])).
% 1.82/1.18  tff(c_110, plain, (![A_18, C_19, B_20]: (k1_tarski(A_18)=C_19 | k1_xboole_0=C_19 | k2_xboole_0(B_20, C_19)!=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.18  tff(c_113, plain, (![A_18]: (k1_tarski(A_18)='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski(A_18)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_61, c_110])).
% 1.82/1.18  tff(c_115, plain, (![A_21]: (k1_tarski(A_21)='#skF_3' | k1_tarski(A_21)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_113])).
% 1.82/1.18  tff(c_119, plain, (k1_tarski('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_55, c_115])).
% 1.82/1.18  tff(c_120, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_55])).
% 1.82/1.18  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_120])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 20
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 0
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 5
% 1.82/1.18  #Demod        : 9
% 1.82/1.18  #Tautology    : 14
% 1.82/1.18  #SimpNegUnit  : 6
% 1.82/1.18  #BackRed      : 3
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.27
% 1.82/1.18  Parsing              : 0.15
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.11
% 1.82/1.18  Inferencing          : 0.04
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.02
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.02
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.41
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
