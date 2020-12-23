%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_18,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_63,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_xboole_0(k1_enumset1(A_39,B_40,C_41),k1_tarski(D_42)) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_9,B_10,D_42] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(D_42)) = k2_enumset1(A_9,A_9,B_10,D_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_79,plain,(
    ! [A_43,B_44,D_45] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(D_45)) = k1_enumset1(A_43,B_44,D_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_91,plain,(
    ! [A_8,D_45] : k2_xboole_0(k1_tarski(A_8),k1_tarski(D_45)) = k1_enumset1(A_8,A_8,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_79])).

tff(c_95,plain,(
    ! [A_46,D_47] : k2_xboole_0(k1_tarski(A_46),k1_tarski(D_47)) = k2_tarski(A_46,D_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_91])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_48,C_49,D_50] :
      ( r1_tarski(k1_tarski(A_48),C_49)
      | ~ r1_tarski(k2_tarski(A_48,D_50),C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2])).

tff(c_114,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_14,plain,(
    ! [C_20,A_18,B_19] :
      ( C_20 = A_18
      | B_19 = A_18
      | ~ r1_tarski(k1_tarski(A_18),k2_tarski(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_114,c_14])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:13:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.17  
% 1.79/1.17  %Foreground sorts:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Background operators:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Foreground operators:
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.17  
% 1.79/1.18  tff(f_58, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.79/1.18  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.79/1.18  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.79/1.18  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.79/1.18  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.79/1.18  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.79/1.18  tff(f_48, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.79/1.18  tff(c_18, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.18  tff(c_16, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.18  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.18  tff(c_8, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.18  tff(c_6, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.18  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.18  tff(c_63, plain, (![A_39, B_40, C_41, D_42]: (k2_xboole_0(k1_enumset1(A_39, B_40, C_41), k1_tarski(D_42))=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.18  tff(c_75, plain, (![A_9, B_10, D_42]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(D_42))=k2_enumset1(A_9, A_9, B_10, D_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 1.79/1.18  tff(c_79, plain, (![A_43, B_44, D_45]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(D_45))=k1_enumset1(A_43, B_44, D_45))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_75])).
% 1.79/1.18  tff(c_91, plain, (![A_8, D_45]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(D_45))=k1_enumset1(A_8, A_8, D_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_79])).
% 1.79/1.18  tff(c_95, plain, (![A_46, D_47]: (k2_xboole_0(k1_tarski(A_46), k1_tarski(D_47))=k2_tarski(A_46, D_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_91])).
% 1.79/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.18  tff(c_107, plain, (![A_48, C_49, D_50]: (r1_tarski(k1_tarski(A_48), C_49) | ~r1_tarski(k2_tarski(A_48, D_50), C_49))), inference(superposition, [status(thm), theory('equality')], [c_95, c_2])).
% 1.79/1.18  tff(c_114, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_107])).
% 1.79/1.18  tff(c_14, plain, (![C_20, A_18, B_19]: (C_20=A_18 | B_19=A_18 | ~r1_tarski(k1_tarski(A_18), k2_tarski(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.79/1.18  tff(c_117, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_114, c_14])).
% 1.79/1.18  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_117])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 23
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 0
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.18  
% 1.79/1.18  Ordering : KBO
% 1.79/1.18  
% 1.79/1.18  Simplification rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Subsume      : 0
% 1.79/1.18  #Demod        : 2
% 1.79/1.18  #Tautology    : 15
% 1.79/1.18  #SimpNegUnit  : 1
% 1.79/1.18  #BackRed      : 0
% 1.79/1.18  
% 1.79/1.18  #Partial instantiations: 0
% 1.79/1.18  #Strategies tried      : 1
% 1.79/1.18  
% 1.79/1.18  Timing (in seconds)
% 1.79/1.18  ----------------------
% 1.85/1.18  Preprocessing        : 0.27
% 1.85/1.18  Parsing              : 0.15
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.13
% 1.85/1.18  Inferencing          : 0.06
% 1.85/1.18  Reduction            : 0.04
% 1.85/1.18  Demodulation         : 0.03
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.02
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.43
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
