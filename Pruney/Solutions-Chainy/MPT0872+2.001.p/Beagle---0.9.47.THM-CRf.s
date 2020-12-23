%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:26 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  49 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k4_tarski(k4_tarski(A,B),C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k3_mcart_1(k4_tarski(A,B),C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

tff(c_8,plain,(
    ! [A_22,B_23,C_24,D_25] : k4_tarski(k3_mcart_1(A_22,B_23,C_24),D_25) = k4_mcart_1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [A_39,B_40,C_41,D_42] : k4_tarski(k3_mcart_1(A_39,B_40,C_41),D_42) = k4_mcart_1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_38,plain,(
    ! [A_39,B_40,C_41,D_42] : k1_mcart_1(k4_mcart_1(A_39,B_40,C_41,D_42)) = k3_mcart_1(A_39,B_40,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_15])).

tff(c_44,plain,(
    ! [A_43,B_44,C_45,D_46] : k4_tarski(k4_tarski(k4_tarski(A_43,B_44),C_45),D_46) = k4_mcart_1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_43,B_44,C_45,D_46] : k4_tarski(k4_tarski(A_43,B_44),C_45) = k1_mcart_1(k4_mcart_1(A_43,B_44,C_45,D_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_15])).

tff(c_83,plain,(
    ! [A_43,B_44,C_45] : k4_tarski(k4_tarski(A_43,B_44),C_45) = k3_mcart_1(A_43,B_44,C_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_86,plain,(
    ! [A_51,B_52,C_53] : k4_tarski(k4_tarski(A_51,B_52),C_53) = k3_mcart_1(A_51,B_52,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_101,plain,(
    ! [A_43,B_44,C_45,C_53] : k3_mcart_1(k4_tarski(A_43,B_44),C_45,C_53) = k4_tarski(k3_mcart_1(A_43,B_44,C_45),C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_86])).

tff(c_110,plain,(
    ! [A_43,B_44,C_45,C_53] : k3_mcart_1(k4_tarski(A_43,B_44),C_45,C_53) = k4_mcart_1(A_43,B_44,C_45,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_101])).

tff(c_12,plain,(
    k3_mcart_1(k4_tarski('#skF_3','#skF_4'),'#skF_5','#skF_6') != k4_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:42:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.16  %$ k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.66/1.16  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.66/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.66/1.16  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.16  
% 1.66/1.17  tff(f_38, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 1.66/1.17  tff(f_36, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_mcart_1)).
% 1.66/1.17  tff(f_40, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k4_tarski(k4_tarski(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 1.66/1.17  tff(f_43, negated_conjecture, ~(![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k3_mcart_1(k4_tarski(A, B), C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_mcart_1)).
% 1.66/1.17  tff(c_8, plain, (![A_22, B_23, C_24, D_25]: (k4_tarski(k3_mcart_1(A_22, B_23, C_24), D_25)=k4_mcart_1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.17  tff(c_29, plain, (![A_39, B_40, C_41, D_42]: (k4_tarski(k3_mcart_1(A_39, B_40, C_41), D_42)=k4_mcart_1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.17  tff(c_2, plain, (![C_20, D_21, B_13, C_14]: (k1_mcart_1(k4_tarski(C_20, D_21))=C_20 | k4_tarski(C_20, D_21)!=k4_tarski(B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.17  tff(c_15, plain, (![B_13, C_14]: (k1_mcart_1(k4_tarski(B_13, C_14))=B_13)), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 1.66/1.17  tff(c_38, plain, (![A_39, B_40, C_41, D_42]: (k1_mcart_1(k4_mcart_1(A_39, B_40, C_41, D_42))=k3_mcart_1(A_39, B_40, C_41))), inference(superposition, [status(thm), theory('equality')], [c_29, c_15])).
% 1.66/1.17  tff(c_44, plain, (![A_43, B_44, C_45, D_46]: (k4_tarski(k4_tarski(k4_tarski(A_43, B_44), C_45), D_46)=k4_mcart_1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.17  tff(c_59, plain, (![A_43, B_44, C_45, D_46]: (k4_tarski(k4_tarski(A_43, B_44), C_45)=k1_mcart_1(k4_mcart_1(A_43, B_44, C_45, D_46)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_15])).
% 1.66/1.17  tff(c_83, plain, (![A_43, B_44, C_45]: (k4_tarski(k4_tarski(A_43, B_44), C_45)=k3_mcart_1(A_43, B_44, C_45))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59])).
% 1.66/1.17  tff(c_86, plain, (![A_51, B_52, C_53]: (k4_tarski(k4_tarski(A_51, B_52), C_53)=k3_mcart_1(A_51, B_52, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59])).
% 1.66/1.17  tff(c_101, plain, (![A_43, B_44, C_45, C_53]: (k3_mcart_1(k4_tarski(A_43, B_44), C_45, C_53)=k4_tarski(k3_mcart_1(A_43, B_44, C_45), C_53))), inference(superposition, [status(thm), theory('equality')], [c_83, c_86])).
% 1.66/1.17  tff(c_110, plain, (![A_43, B_44, C_45, C_53]: (k3_mcart_1(k4_tarski(A_43, B_44), C_45, C_53)=k4_mcart_1(A_43, B_44, C_45, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_101])).
% 1.66/1.17  tff(c_12, plain, (k3_mcart_1(k4_tarski('#skF_3', '#skF_4'), '#skF_5', '#skF_6')!=k4_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.17  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_12])).
% 1.66/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  Inference rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Ref     : 1
% 1.66/1.17  #Sup     : 46
% 1.66/1.17  #Fact    : 0
% 1.66/1.17  #Define  : 0
% 1.66/1.17  #Split   : 0
% 1.66/1.17  #Chain   : 0
% 1.66/1.17  #Close   : 0
% 1.66/1.17  
% 1.66/1.17  Ordering : KBO
% 1.66/1.17  
% 1.66/1.17  Simplification rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Subsume      : 0
% 1.66/1.17  #Demod        : 19
% 1.66/1.17  #Tautology    : 19
% 1.66/1.17  #SimpNegUnit  : 0
% 1.66/1.17  #BackRed      : 2
% 1.66/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.66/1.17  Preprocessing        : 0.26
% 1.66/1.17  Parsing              : 0.14
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.16
% 1.66/1.17  Inferencing          : 0.08
% 1.66/1.17  Reduction            : 0.05
% 1.66/1.17  Demodulation         : 0.04
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.02
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.18  Cooper               : 0.00
% 1.66/1.18  Total                : 0.45
% 1.66/1.18  Index Insertion      : 0.00
% 1.66/1.18  Index Deletion       : 0.00
% 1.66/1.18  Index Matching       : 0.00
% 1.66/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
