%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  77 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F)
          & r1_tarski(G,H) )
       => r1_tarski(k4_zfmisc_1(A,C,E,G),k4_zfmisc_1(B,D,F,H)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_23,C_24,B_25,D_26] :
      ( r1_tarski(k2_zfmisc_1(A_23,C_24),k2_zfmisc_1(B_25,D_26))
      | ~ r1_tarski(C_24,D_26)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_46,B_42,C_45,D_43,B_44] :
      ( r1_tarski(k3_zfmisc_1(A_46,B_44,C_45),k2_zfmisc_1(B_42,D_43))
      | ~ r1_tarski(C_45,D_43)
      | ~ r1_tarski(k2_zfmisc_1(A_46,B_44),B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_146,plain,(
    ! [A_46,B_6,C_7,A_5,C_45,B_44] :
      ( r1_tarski(k3_zfmisc_1(A_46,B_44,C_45),k3_zfmisc_1(A_5,B_6,C_7))
      | ~ r1_tarski(C_45,C_7)
      | ~ r1_tarski(k2_zfmisc_1(A_46,B_44),k2_zfmisc_1(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_134])).

tff(c_10,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    ! [A_50,B_49,D_52,C_51,C_47,A_48] :
      ( r1_tarski(k2_zfmisc_1(A_50,C_47),k4_zfmisc_1(A_48,B_49,C_51,D_52))
      | ~ r1_tarski(C_47,D_52)
      | ~ r1_tarski(A_50,k3_zfmisc_1(A_48,B_49,C_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_253,plain,(
    ! [A_87,D_92,C_85,A_88,C_91,B_89,B_86,D_90] :
      ( r1_tarski(k4_zfmisc_1(A_88,B_89,C_91,D_92),k4_zfmisc_1(A_87,B_86,C_85,D_90))
      | ~ r1_tarski(D_92,D_90)
      | ~ r1_tarski(k3_zfmisc_1(A_88,B_89,C_91),k3_zfmisc_1(A_87,B_86,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_149])).

tff(c_8,plain,(
    ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_3','#skF_5','#skF_7'),k4_zfmisc_1('#skF_2','#skF_4','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_256,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_253,c_8])).

tff(c_271,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_256])).

tff(c_278,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_146,c_271])).

tff(c_281,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_278])).

tff(c_284,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_281])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.27  %$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.26/1.27  
% 2.26/1.27  %Foreground sorts:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Background operators:
% 2.26/1.27  
% 2.26/1.27  
% 2.26/1.27  %Foreground operators:
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.27  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.26/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.27  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.26/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.27  
% 2.26/1.28  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) & r1_tarski(G, H)) => r1_tarski(k4_zfmisc_1(A, C, E, G), k4_zfmisc_1(B, D, F, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_mcart_1)).
% 2.26/1.28  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.26/1.28  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.26/1.28  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 2.26/1.28  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.28  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.28  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.28  tff(c_12, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.28  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.28  tff(c_64, plain, (![A_23, C_24, B_25, D_26]: (r1_tarski(k2_zfmisc_1(A_23, C_24), k2_zfmisc_1(B_25, D_26)) | ~r1_tarski(C_24, D_26) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.28  tff(c_134, plain, (![A_46, B_42, C_45, D_43, B_44]: (r1_tarski(k3_zfmisc_1(A_46, B_44, C_45), k2_zfmisc_1(B_42, D_43)) | ~r1_tarski(C_45, D_43) | ~r1_tarski(k2_zfmisc_1(A_46, B_44), B_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 2.26/1.28  tff(c_146, plain, (![A_46, B_6, C_7, A_5, C_45, B_44]: (r1_tarski(k3_zfmisc_1(A_46, B_44, C_45), k3_zfmisc_1(A_5, B_6, C_7)) | ~r1_tarski(C_45, C_7) | ~r1_tarski(k2_zfmisc_1(A_46, B_44), k2_zfmisc_1(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_134])).
% 2.26/1.28  tff(c_10, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.28  tff(c_6, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.28  tff(c_149, plain, (![A_50, B_49, D_52, C_51, C_47, A_48]: (r1_tarski(k2_zfmisc_1(A_50, C_47), k4_zfmisc_1(A_48, B_49, C_51, D_52)) | ~r1_tarski(C_47, D_52) | ~r1_tarski(A_50, k3_zfmisc_1(A_48, B_49, C_51)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 2.26/1.28  tff(c_253, plain, (![A_87, D_92, C_85, A_88, C_91, B_89, B_86, D_90]: (r1_tarski(k4_zfmisc_1(A_88, B_89, C_91, D_92), k4_zfmisc_1(A_87, B_86, C_85, D_90)) | ~r1_tarski(D_92, D_90) | ~r1_tarski(k3_zfmisc_1(A_88, B_89, C_91), k3_zfmisc_1(A_87, B_86, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_149])).
% 2.26/1.28  tff(c_8, plain, (~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_3', '#skF_5', '#skF_7'), k4_zfmisc_1('#skF_2', '#skF_4', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.28  tff(c_256, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_253, c_8])).
% 2.26/1.28  tff(c_271, plain, (~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_256])).
% 2.26/1.28  tff(c_278, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_146, c_271])).
% 2.26/1.28  tff(c_281, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_278])).
% 2.26/1.28  tff(c_284, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_281])).
% 2.26/1.28  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_284])).
% 2.26/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  
% 2.26/1.28  Inference rules
% 2.26/1.28  ----------------------
% 2.26/1.28  #Ref     : 0
% 2.26/1.28  #Sup     : 65
% 2.26/1.28  #Fact    : 0
% 2.26/1.28  #Define  : 0
% 2.26/1.28  #Split   : 0
% 2.26/1.28  #Chain   : 0
% 2.26/1.28  #Close   : 0
% 2.26/1.28  
% 2.26/1.28  Ordering : KBO
% 2.26/1.28  
% 2.26/1.28  Simplification rules
% 2.26/1.28  ----------------------
% 2.26/1.28  #Subsume      : 26
% 2.26/1.28  #Demod        : 53
% 2.26/1.28  #Tautology    : 22
% 2.26/1.28  #SimpNegUnit  : 0
% 2.26/1.28  #BackRed      : 0
% 2.26/1.28  
% 2.26/1.28  #Partial instantiations: 0
% 2.26/1.28  #Strategies tried      : 1
% 2.26/1.28  
% 2.26/1.28  Timing (in seconds)
% 2.26/1.28  ----------------------
% 2.26/1.28  Preprocessing        : 0.25
% 2.26/1.28  Parsing              : 0.14
% 2.26/1.28  CNF conversion       : 0.02
% 2.26/1.28  Main loop            : 0.25
% 2.26/1.28  Inferencing          : 0.11
% 2.26/1.28  Reduction            : 0.08
% 2.26/1.28  Demodulation         : 0.06
% 2.26/1.28  BG Simplification    : 0.01
% 2.26/1.28  Subsumption          : 0.04
% 2.26/1.28  Abstraction          : 0.02
% 2.26/1.28  MUC search           : 0.00
% 2.26/1.28  Cooper               : 0.00
% 2.26/1.28  Total                : 0.52
% 2.26/1.28  Index Insertion      : 0.00
% 2.26/1.28  Index Deletion       : 0.00
% 2.26/1.28  Index Matching       : 0.00
% 2.26/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
