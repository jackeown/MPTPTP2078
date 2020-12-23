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
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   44 (  68 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  75 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k3_xboole_0(B_22,k1_tarski(A_21)) = k1_tarski(A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_23,B_24] : k3_xboole_0(k1_tarski(A_23),k2_tarski(A_23,B_24)) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_3'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_326,plain,(
    ! [A_53,B_54,C_55] : k3_xboole_0(k3_xboole_0(A_53,B_54),C_55) = k3_xboole_0(A_53,k3_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_503,plain,(
    ! [C_59,A_60,B_61] : k3_xboole_0(C_59,k3_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,k3_xboole_0(B_61,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_2])).

tff(c_1853,plain,(
    ! [A_79] : k3_xboole_0('#skF_5',k3_xboole_0(A_79,k2_tarski('#skF_4','#skF_3'))) = k3_xboole_0(A_79,k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_503])).

tff(c_1942,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1853])).

tff(c_179,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | k3_xboole_0(A_39,k1_tarski(B_38)) != k1_tarski(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_186,plain,(
    ! [B_38,A_1] :
      ( r2_hidden(B_38,A_1)
      | k3_xboole_0(k1_tarski(B_38),A_1) != k1_tarski(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_2122,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1942,c_186])).

tff(c_4475,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2122])).

tff(c_4478,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4475])).

tff(c_4482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4478])).

tff(c_4483,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2122])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4487,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4483,c_8])).

tff(c_4491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.35  
% 5.81/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.35  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.81/2.35  
% 5.81/2.35  %Foreground sorts:
% 5.81/2.35  
% 5.81/2.35  
% 5.81/2.35  %Background operators:
% 5.81/2.35  
% 5.81/2.35  
% 5.81/2.35  %Foreground operators:
% 5.81/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.81/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.81/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.81/2.35  tff('#skF_5', type, '#skF_5': $i).
% 5.81/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.81/2.35  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.35  tff('#skF_4', type, '#skF_4': $i).
% 5.81/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.81/2.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.81/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.35  
% 5.81/2.36  tff(f_63, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 5.81/2.36  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.81/2.36  tff(f_54, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 5.81/2.36  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.81/2.36  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.81/2.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.81/2.36  tff(f_48, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 5.81/2.36  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.81/2.36  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.81/2.36  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.81/2.36  tff(c_28, plain, (![B_22, A_21]: (k3_xboole_0(B_22, k1_tarski(A_21))=k1_tarski(A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.81/2.36  tff(c_30, plain, (![A_23, B_24]: (k3_xboole_0(k1_tarski(A_23), k2_tarski(A_23, B_24))=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.81/2.36  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.81/2.36  tff(c_36, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.81/2.36  tff(c_37, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_3'), '#skF_5')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_36])).
% 5.81/2.36  tff(c_326, plain, (![A_53, B_54, C_55]: (k3_xboole_0(k3_xboole_0(A_53, B_54), C_55)=k3_xboole_0(A_53, k3_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.81/2.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.81/2.36  tff(c_503, plain, (![C_59, A_60, B_61]: (k3_xboole_0(C_59, k3_xboole_0(A_60, B_61))=k3_xboole_0(A_60, k3_xboole_0(B_61, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_326, c_2])).
% 5.81/2.36  tff(c_1853, plain, (![A_79]: (k3_xboole_0('#skF_5', k3_xboole_0(A_79, k2_tarski('#skF_4', '#skF_3')))=k3_xboole_0(A_79, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_37, c_503])).
% 5.81/2.36  tff(c_1942, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1853])).
% 5.81/2.36  tff(c_179, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | k3_xboole_0(A_39, k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.81/2.36  tff(c_186, plain, (![B_38, A_1]: (r2_hidden(B_38, A_1) | k3_xboole_0(k1_tarski(B_38), A_1)!=k1_tarski(B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 5.81/2.36  tff(c_2122, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1942, c_186])).
% 5.81/2.36  tff(c_4475, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_2122])).
% 5.81/2.36  tff(c_4478, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_4475])).
% 5.81/2.36  tff(c_4482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4478])).
% 5.81/2.36  tff(c_4483, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_2122])).
% 5.81/2.36  tff(c_8, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.81/2.36  tff(c_4487, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4483, c_8])).
% 5.81/2.36  tff(c_4491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_4487])).
% 5.81/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.36  
% 5.81/2.36  Inference rules
% 5.81/2.36  ----------------------
% 5.81/2.36  #Ref     : 0
% 5.81/2.36  #Sup     : 1156
% 5.81/2.36  #Fact    : 0
% 5.81/2.36  #Define  : 0
% 5.81/2.36  #Split   : 2
% 5.81/2.36  #Chain   : 0
% 5.81/2.36  #Close   : 0
% 5.81/2.36  
% 5.81/2.36  Ordering : KBO
% 5.81/2.36  
% 5.81/2.36  Simplification rules
% 5.81/2.36  ----------------------
% 5.81/2.36  #Subsume      : 163
% 5.81/2.36  #Demod        : 585
% 5.81/2.36  #Tautology    : 283
% 5.81/2.36  #SimpNegUnit  : 2
% 5.81/2.36  #BackRed      : 0
% 5.81/2.36  
% 5.81/2.36  #Partial instantiations: 0
% 5.81/2.36  #Strategies tried      : 1
% 5.81/2.36  
% 5.81/2.36  Timing (in seconds)
% 5.81/2.36  ----------------------
% 5.81/2.36  Preprocessing        : 0.31
% 5.81/2.36  Parsing              : 0.16
% 5.81/2.36  CNF conversion       : 0.02
% 5.81/2.36  Main loop            : 1.28
% 5.81/2.36  Inferencing          : 0.30
% 5.81/2.36  Reduction            : 0.73
% 5.81/2.36  Demodulation         : 0.66
% 5.81/2.36  BG Simplification    : 0.05
% 5.81/2.36  Subsumption          : 0.15
% 5.81/2.36  Abstraction          : 0.06
% 5.81/2.36  MUC search           : 0.00
% 5.81/2.36  Cooper               : 0.00
% 5.81/2.36  Total                : 1.62
% 5.81/2.36  Index Insertion      : 0.00
% 5.81/2.36  Index Deletion       : 0.00
% 5.81/2.36  Index Matching       : 0.00
% 5.81/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
