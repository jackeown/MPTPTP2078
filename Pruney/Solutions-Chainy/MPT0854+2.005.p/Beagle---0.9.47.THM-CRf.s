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
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   41 (  61 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  90 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_16,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [A_71,B_72,C_73] :
      ( k4_tarski('#skF_1'(A_71,B_72,C_73),'#skF_2'(A_71,B_72,C_73)) = A_71
      | ~ r2_hidden(A_71,k2_zfmisc_1(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_250,plain,(
    ! [C_89,C_92,D_88,B_91,A_90] :
      ( r2_hidden('#skF_2'(A_90,B_91,C_92),D_88)
      | ~ r2_hidden(A_90,k2_zfmisc_1(C_89,D_88))
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_91,C_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_6])).

tff(c_264,plain,(
    ! [B_98,C_99] :
      ( r2_hidden('#skF_2'('#skF_3',B_98,C_99),'#skF_5')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_98,C_99)) ) ),
    inference(resolution,[status(thm)],[c_16,c_250])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_mcart_1(k4_tarski(A_10,B_11)) = B_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_mcart_1(A_74) = '#skF_2'(A_74,B_75,C_76)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_199,plain,(
    k2_mcart_1('#skF_3') = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_190])).

tff(c_47,plain,(
    ! [A_28,B_29,C_30] :
      ( k4_tarski('#skF_1'(A_28,B_29,C_30),'#skF_2'(A_28,B_29,C_30)) = A_28
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [B_56,A_52,C_53,D_54,C_55] :
      ( r2_hidden('#skF_1'(A_52,B_56,C_53),C_55)
      | ~ r2_hidden(A_52,k2_zfmisc_1(C_55,D_54))
      | ~ r2_hidden(A_52,k2_zfmisc_1(B_56,C_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_8])).

tff(c_145,plain,(
    ! [B_57,C_58] :
      ( r2_hidden('#skF_1'('#skF_3',B_57,C_58),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_57,C_58)) ) ),
    inference(resolution,[status(thm)],[c_16,c_138])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_mcart_1(k4_tarski(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_mcart_1(A_34) = '#skF_1'(A_34,B_35,C_36)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_94,plain,(
    k1_mcart_1('#skF_3') = '#skF_1'('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_14,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_35,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_35])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_145,c_95])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_148])).

tff(c_153,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_200,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_153])).

tff(c_267,plain,(
    ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_264,c_200])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.06/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.06/1.32  
% 2.06/1.33  tff(f_49, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.06/1.33  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.06/1.33  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.06/1.33  tff(f_42, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.06/1.33  tff(c_16, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.33  tff(c_166, plain, (![A_71, B_72, C_73]: (k4_tarski('#skF_1'(A_71, B_72, C_73), '#skF_2'(A_71, B_72, C_73))=A_71 | ~r2_hidden(A_71, k2_zfmisc_1(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.33  tff(c_6, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.33  tff(c_250, plain, (![C_89, C_92, D_88, B_91, A_90]: (r2_hidden('#skF_2'(A_90, B_91, C_92), D_88) | ~r2_hidden(A_90, k2_zfmisc_1(C_89, D_88)) | ~r2_hidden(A_90, k2_zfmisc_1(B_91, C_92)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_6])).
% 2.06/1.33  tff(c_264, plain, (![B_98, C_99]: (r2_hidden('#skF_2'('#skF_3', B_98, C_99), '#skF_5') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_98, C_99)))), inference(resolution, [status(thm)], [c_16, c_250])).
% 2.06/1.33  tff(c_12, plain, (![A_10, B_11]: (k2_mcart_1(k4_tarski(A_10, B_11))=B_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.33  tff(c_190, plain, (![A_74, B_75, C_76]: (k2_mcart_1(A_74)='#skF_2'(A_74, B_75, C_76) | ~r2_hidden(A_74, k2_zfmisc_1(B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 2.06/1.33  tff(c_199, plain, (k2_mcart_1('#skF_3')='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_190])).
% 2.06/1.33  tff(c_47, plain, (![A_28, B_29, C_30]: (k4_tarski('#skF_1'(A_28, B_29, C_30), '#skF_2'(A_28, B_29, C_30))=A_28 | ~r2_hidden(A_28, k2_zfmisc_1(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.33  tff(c_8, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.33  tff(c_138, plain, (![B_56, A_52, C_53, D_54, C_55]: (r2_hidden('#skF_1'(A_52, B_56, C_53), C_55) | ~r2_hidden(A_52, k2_zfmisc_1(C_55, D_54)) | ~r2_hidden(A_52, k2_zfmisc_1(B_56, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_8])).
% 2.06/1.33  tff(c_145, plain, (![B_57, C_58]: (r2_hidden('#skF_1'('#skF_3', B_57, C_58), '#skF_4') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_57, C_58)))), inference(resolution, [status(thm)], [c_16, c_138])).
% 2.06/1.33  tff(c_10, plain, (![A_10, B_11]: (k1_mcart_1(k4_tarski(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.33  tff(c_85, plain, (![A_34, B_35, C_36]: (k1_mcart_1(A_34)='#skF_1'(A_34, B_35, C_36) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 2.06/1.33  tff(c_94, plain, (k1_mcart_1('#skF_3')='#skF_1'('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_85])).
% 2.06/1.33  tff(c_14, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.33  tff(c_35, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_14])).
% 2.06/1.33  tff(c_95, plain, (~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_35])).
% 2.06/1.33  tff(c_148, plain, (~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_145, c_95])).
% 2.06/1.33  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_148])).
% 2.06/1.33  tff(c_153, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_14])).
% 2.06/1.33  tff(c_200, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_153])).
% 2.06/1.33  tff(c_267, plain, (~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_264, c_200])).
% 2.06/1.33  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_267])).
% 2.06/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.33  
% 2.06/1.33  Inference rules
% 2.06/1.33  ----------------------
% 2.06/1.33  #Ref     : 0
% 2.06/1.33  #Sup     : 64
% 2.06/1.33  #Fact    : 0
% 2.06/1.33  #Define  : 0
% 2.06/1.33  #Split   : 1
% 2.06/1.33  #Chain   : 0
% 2.06/1.33  #Close   : 0
% 2.06/1.33  
% 2.06/1.33  Ordering : KBO
% 2.06/1.33  
% 2.06/1.33  Simplification rules
% 2.06/1.33  ----------------------
% 2.06/1.33  #Subsume      : 0
% 2.06/1.33  #Demod        : 9
% 2.06/1.33  #Tautology    : 28
% 2.06/1.33  #SimpNegUnit  : 0
% 2.06/1.33  #BackRed      : 3
% 2.06/1.33  
% 2.06/1.33  #Partial instantiations: 0
% 2.06/1.33  #Strategies tried      : 1
% 2.06/1.33  
% 2.06/1.33  Timing (in seconds)
% 2.06/1.33  ----------------------
% 2.06/1.33  Preprocessing        : 0.29
% 2.06/1.33  Parsing              : 0.16
% 2.06/1.33  CNF conversion       : 0.02
% 2.06/1.33  Main loop            : 0.22
% 2.06/1.33  Inferencing          : 0.10
% 2.06/1.33  Reduction            : 0.06
% 2.06/1.34  Demodulation         : 0.04
% 2.06/1.34  BG Simplification    : 0.01
% 2.06/1.34  Subsumption          : 0.03
% 2.06/1.34  Abstraction          : 0.01
% 2.06/1.34  MUC search           : 0.00
% 2.06/1.34  Cooper               : 0.00
% 2.06/1.34  Total                : 0.54
% 2.06/1.34  Index Insertion      : 0.00
% 2.06/1.34  Index Deletion       : 0.00
% 2.06/1.34  Index Matching       : 0.00
% 2.06/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
