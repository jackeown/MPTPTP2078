%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  67 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F)
          & r1_tarski(G,H) )
       => r1_tarski(k4_zfmisc_1(A,C,E,G),k4_zfmisc_1(B,D,F,H)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_tarski(E,F) )
     => r1_tarski(k3_zfmisc_1(A,C,E),k3_zfmisc_1(B,D,F)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,B),C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( r1_tarski(k3_zfmisc_1(A_12,C_14,E_16),k3_zfmisc_1(B_13,D_15,F_17))
      | ~ r1_tarski(E_16,F_17)
      | ~ r1_tarski(C_14,D_15)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_67,plain,(
    ! [A_29,C_30,B_31,D_32] :
      ( r1_tarski(k2_zfmisc_1(A_29,C_30),k2_zfmisc_1(B_31,D_32))
      | ~ r1_tarski(C_30,D_32)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [C_75,C_73,B_74,A_72,A_71,D_76] :
      ( r1_tarski(k2_zfmisc_1(A_72,C_73),k4_zfmisc_1(A_71,B_74,C_75,D_76))
      | ~ r1_tarski(C_73,D_76)
      | ~ r1_tarski(A_72,k3_zfmisc_1(A_71,B_74,C_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_67])).

tff(c_299,plain,(
    ! [B_115,A_113,A_112,C_111,D_114,D_118,B_116,C_117] :
      ( r1_tarski(k4_zfmisc_1(A_112,B_115,C_117,D_118),k4_zfmisc_1(A_113,B_116,C_111,D_114))
      | ~ r1_tarski(D_118,D_114)
      | ~ r1_tarski(k3_zfmisc_1(A_112,B_115,C_117),k3_zfmisc_1(A_113,B_116,C_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19,c_200])).

tff(c_10,plain,(
    ~ r1_tarski(k4_zfmisc_1('#skF_1','#skF_3','#skF_5','#skF_7'),k4_zfmisc_1('#skF_2','#skF_4','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_302,plain,
    ( ~ r1_tarski('#skF_7','#skF_8')
    | ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_299,c_10])).

tff(c_317,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_302])).

tff(c_327,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_317])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n001.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 13:51:44 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.25  %$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.21/1.25  
% 2.21/1.25  %Foreground sorts:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Background operators:
% 2.21/1.25  
% 2.21/1.25  
% 2.21/1.25  %Foreground operators:
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.25  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.21/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.25  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.21/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.25  
% 2.21/1.26  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) & r1_tarski(G, H)) => r1_tarski(k4_zfmisc_1(A, C, E, G), k4_zfmisc_1(B, D, F, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_mcart_1)).
% 2.21/1.26  tff(f_43, axiom, (![A, B, C, D, E, F]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) => r1_tarski(k3_zfmisc_1(A, C, E), k3_zfmisc_1(B, D, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_mcart_1)).
% 2.21/1.26  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.21/1.26  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_mcart_1)).
% 2.21/1.26  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 2.21/1.26  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.26  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.26  tff(c_14, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.26  tff(c_8, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (r1_tarski(k3_zfmisc_1(A_12, C_14, E_16), k3_zfmisc_1(B_13, D_15, F_17)) | ~r1_tarski(E_16, F_17) | ~r1_tarski(C_14, D_15) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.26  tff(c_12, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.26  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.26  tff(c_6, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.26  tff(c_19, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.21/1.26  tff(c_67, plain, (![A_29, C_30, B_31, D_32]: (r1_tarski(k2_zfmisc_1(A_29, C_30), k2_zfmisc_1(B_31, D_32)) | ~r1_tarski(C_30, D_32) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.26  tff(c_200, plain, (![C_75, C_73, B_74, A_72, A_71, D_76]: (r1_tarski(k2_zfmisc_1(A_72, C_73), k4_zfmisc_1(A_71, B_74, C_75, D_76)) | ~r1_tarski(C_73, D_76) | ~r1_tarski(A_72, k3_zfmisc_1(A_71, B_74, C_75)))), inference(superposition, [status(thm), theory('equality')], [c_19, c_67])).
% 2.21/1.26  tff(c_299, plain, (![B_115, A_113, A_112, C_111, D_114, D_118, B_116, C_117]: (r1_tarski(k4_zfmisc_1(A_112, B_115, C_117, D_118), k4_zfmisc_1(A_113, B_116, C_111, D_114)) | ~r1_tarski(D_118, D_114) | ~r1_tarski(k3_zfmisc_1(A_112, B_115, C_117), k3_zfmisc_1(A_113, B_116, C_111)))), inference(superposition, [status(thm), theory('equality')], [c_19, c_200])).
% 2.21/1.26  tff(c_10, plain, (~r1_tarski(k4_zfmisc_1('#skF_1', '#skF_3', '#skF_5', '#skF_7'), k4_zfmisc_1('#skF_2', '#skF_4', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.26  tff(c_302, plain, (~r1_tarski('#skF_7', '#skF_8') | ~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_299, c_10])).
% 2.21/1.26  tff(c_317, plain, (~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_302])).
% 2.21/1.26  tff(c_327, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_317])).
% 2.21/1.26  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_327])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 77
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 0
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 25
% 2.21/1.26  #Demod        : 59
% 2.21/1.26  #Tautology    : 22
% 2.21/1.26  #SimpNegUnit  : 0
% 2.21/1.26  #BackRed      : 0
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.27  Preprocessing        : 0.26
% 2.21/1.27  Parsing              : 0.14
% 2.21/1.27  CNF conversion       : 0.02
% 2.21/1.27  Main loop            : 0.26
% 2.21/1.27  Inferencing          : 0.12
% 2.21/1.27  Reduction            : 0.08
% 2.21/1.27  Demodulation         : 0.07
% 2.21/1.27  BG Simplification    : 0.01
% 2.21/1.27  Subsumption          : 0.04
% 2.21/1.27  Abstraction          : 0.02
% 2.21/1.27  MUC search           : 0.00
% 2.21/1.27  Cooper               : 0.00
% 2.21/1.27  Total                : 0.55
% 2.21/1.27  Index Insertion      : 0.00
% 2.21/1.27  Index Deletion       : 0.00
% 2.21/1.27  Index Matching       : 0.00
% 2.21/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
