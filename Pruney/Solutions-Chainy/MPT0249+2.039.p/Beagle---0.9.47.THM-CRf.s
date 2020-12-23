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
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   47 (  87 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 140 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_41])).

tff(c_85,plain,(
    ! [B_32,A_33] :
      ( k1_tarski(B_32) = A_33
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,k1_tarski(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_98,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_88])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_71,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_115,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_71])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_115])).

tff(c_121,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_124,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_32])).

tff(c_8,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(A_42,k2_xboole_0(B_43,C_44))
      | ~ r1_tarski(k4_xboole_0(A_42,B_43),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [A_42,B_43] : r1_tarski(A_42,k2_xboole_0(B_43,k4_xboole_0(A_42,B_43))) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_207,plain,(
    ! [A_45,B_46] : r1_tarski(A_45,k2_xboole_0(B_46,A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_203])).

tff(c_219,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_207])).

tff(c_163,plain,(
    ! [B_39,A_40] :
      ( k1_tarski(B_39) = A_40
      | k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,k1_tarski(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,(
    ! [A_40] :
      ( k1_tarski('#skF_1') = A_40
      | k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_163])).

tff(c_174,plain,(
    ! [A_40] :
      ( A_40 = '#skF_2'
      | k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_166])).

tff(c_224,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_219,c_174])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_30,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:10:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.31  
% 2.09/1.31  %Foreground sorts:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Background operators:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Foreground operators:
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  
% 2.16/1.32  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.16/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.32  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.16/1.32  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.16/1.32  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.16/1.32  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.16/1.32  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.32  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.32  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.32  tff(c_32, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.32  tff(c_41, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.32  tff(c_44, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_41])).
% 2.16/1.32  tff(c_85, plain, (![B_32, A_33]: (k1_tarski(B_32)=A_33 | k1_xboole_0=A_33 | ~r1_tarski(A_33, k1_tarski(B_32)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.32  tff(c_88, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_44, c_85])).
% 2.16/1.32  tff(c_98, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_28, c_88])).
% 2.16/1.32  tff(c_54, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.32  tff(c_63, plain, (k1_tarski('#skF_1')='#skF_2' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_44, c_54])).
% 2.16/1.32  tff(c_71, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_63])).
% 2.16/1.32  tff(c_115, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_71])).
% 2.16/1.32  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_115])).
% 2.16/1.32  tff(c_121, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_63])).
% 2.16/1.32  tff(c_124, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_32])).
% 2.16/1.32  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.32  tff(c_195, plain, (![A_42, B_43, C_44]: (r1_tarski(A_42, k2_xboole_0(B_43, C_44)) | ~r1_tarski(k4_xboole_0(A_42, B_43), C_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.32  tff(c_203, plain, (![A_42, B_43]: (r1_tarski(A_42, k2_xboole_0(B_43, k4_xboole_0(A_42, B_43))))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.16/1.32  tff(c_207, plain, (![A_45, B_46]: (r1_tarski(A_45, k2_xboole_0(B_46, A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_203])).
% 2.16/1.32  tff(c_219, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_207])).
% 2.16/1.32  tff(c_163, plain, (![B_39, A_40]: (k1_tarski(B_39)=A_40 | k1_xboole_0=A_40 | ~r1_tarski(A_40, k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.32  tff(c_166, plain, (![A_40]: (k1_tarski('#skF_1')=A_40 | k1_xboole_0=A_40 | ~r1_tarski(A_40, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_163])).
% 2.16/1.32  tff(c_174, plain, (![A_40]: (A_40='#skF_2' | k1_xboole_0=A_40 | ~r1_tarski(A_40, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_166])).
% 2.16/1.32  tff(c_224, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_219, c_174])).
% 2.16/1.32  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_30, c_224])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 41
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 1
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 1
% 2.16/1.32  #Demod        : 19
% 2.16/1.32  #Tautology    : 26
% 2.16/1.32  #SimpNegUnit  : 6
% 2.16/1.32  #BackRed      : 5
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.20/1.33  Preprocessing        : 0.33
% 2.20/1.33  Parsing              : 0.17
% 2.20/1.33  CNF conversion       : 0.02
% 2.20/1.33  Main loop            : 0.17
% 2.20/1.33  Inferencing          : 0.05
% 2.20/1.33  Reduction            : 0.06
% 2.20/1.33  Demodulation         : 0.05
% 2.20/1.33  BG Simplification    : 0.01
% 2.20/1.33  Subsumption          : 0.04
% 2.20/1.33  Abstraction          : 0.01
% 2.20/1.33  MUC search           : 0.00
% 2.20/1.33  Cooper               : 0.00
% 2.20/1.33  Total                : 0.53
% 2.20/1.33  Index Insertion      : 0.00
% 2.20/1.33  Index Deletion       : 0.00
% 2.20/1.33  Index Matching       : 0.00
% 2.20/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
