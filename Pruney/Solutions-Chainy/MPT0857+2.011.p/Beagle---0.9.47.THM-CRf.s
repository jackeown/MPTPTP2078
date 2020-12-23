%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   39 (  58 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  89 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_26,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k1_mcart_1(A_32),B_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_78])).

tff(c_83,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_100,plain,(
    ! [A_44,C_45,B_46] :
      ( r2_hidden(k2_mcart_1(A_44),C_45)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_46,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_22,plain,(
    ! [A_17,B_18] : k1_mcart_1(k4_tarski(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( r2_hidden(k4_tarski(A_55,B_56),k2_zfmisc_1(C_57,D_58))
      | ~ r2_hidden(B_56,D_58)
      | ~ r2_hidden(A_55,C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_mcart_1(A_14) = B_15
      | ~ r2_hidden(A_14,k2_zfmisc_1(k1_tarski(B_15),C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [A_55,B_56,B_15,D_58] :
      ( k1_mcart_1(k4_tarski(A_55,B_56)) = B_15
      | ~ r2_hidden(B_56,D_58)
      | ~ r2_hidden(A_55,k1_tarski(B_15)) ) ),
    inference(resolution,[status(thm)],[c_106,c_20])).

tff(c_126,plain,(
    ! [B_15,A_55,B_56,D_58] :
      ( B_15 = A_55
      | ~ r2_hidden(B_56,D_58)
      | ~ r2_hidden(A_55,k1_tarski(B_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_118])).

tff(c_129,plain,(
    ! [B_56,D_58] : ~ r2_hidden(B_56,D_58) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_103])).

tff(c_140,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r2_hidden(A_60,k1_tarski(B_59)) ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_143,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_103,c_140])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.19  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.19  
% 1.75/1.19  %Foreground sorts:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Background operators:
% 1.75/1.19  
% 1.75/1.19  
% 1.75/1.19  %Foreground operators:
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.75/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.75/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.75/1.19  
% 1.75/1.19  tff(f_60, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.75/1.19  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.75/1.19  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.75/1.19  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.75/1.19  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.75/1.19  tff(c_26, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.19  tff(c_65, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 1.75/1.19  tff(c_28, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.75/1.19  tff(c_76, plain, (![A_32, B_33, C_34]: (r2_hidden(k1_mcart_1(A_32), B_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.19  tff(c_78, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_76])).
% 1.75/1.19  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_78])).
% 1.75/1.19  tff(c_83, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.75/1.19  tff(c_100, plain, (![A_44, C_45, B_46]: (r2_hidden(k2_mcart_1(A_44), C_45) | ~r2_hidden(A_44, k2_zfmisc_1(B_46, C_45)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.19  tff(c_103, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_100])).
% 1.75/1.19  tff(c_22, plain, (![A_17, B_18]: (k1_mcart_1(k4_tarski(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.75/1.19  tff(c_106, plain, (![A_55, B_56, C_57, D_58]: (r2_hidden(k4_tarski(A_55, B_56), k2_zfmisc_1(C_57, D_58)) | ~r2_hidden(B_56, D_58) | ~r2_hidden(A_55, C_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.19  tff(c_20, plain, (![A_14, B_15, C_16]: (k1_mcart_1(A_14)=B_15 | ~r2_hidden(A_14, k2_zfmisc_1(k1_tarski(B_15), C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.75/1.19  tff(c_118, plain, (![A_55, B_56, B_15, D_58]: (k1_mcart_1(k4_tarski(A_55, B_56))=B_15 | ~r2_hidden(B_56, D_58) | ~r2_hidden(A_55, k1_tarski(B_15)))), inference(resolution, [status(thm)], [c_106, c_20])).
% 1.75/1.19  tff(c_126, plain, (![B_15, A_55, B_56, D_58]: (B_15=A_55 | ~r2_hidden(B_56, D_58) | ~r2_hidden(A_55, k1_tarski(B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_118])).
% 1.75/1.19  tff(c_129, plain, (![B_56, D_58]: (~r2_hidden(B_56, D_58))), inference(splitLeft, [status(thm)], [c_126])).
% 1.75/1.19  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_103])).
% 1.75/1.19  tff(c_140, plain, (![B_59, A_60]: (B_59=A_60 | ~r2_hidden(A_60, k1_tarski(B_59)))), inference(splitRight, [status(thm)], [c_126])).
% 1.75/1.19  tff(c_143, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_103, c_140])).
% 1.75/1.19  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_143])).
% 1.75/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.19  
% 1.75/1.19  Inference rules
% 1.75/1.19  ----------------------
% 1.75/1.19  #Ref     : 0
% 1.75/1.19  #Sup     : 21
% 1.75/1.19  #Fact    : 0
% 1.75/1.19  #Define  : 0
% 1.75/1.19  #Split   : 2
% 1.75/1.19  #Chain   : 0
% 1.75/1.20  #Close   : 0
% 1.75/1.20  
% 1.75/1.20  Ordering : KBO
% 1.75/1.20  
% 1.75/1.20  Simplification rules
% 1.75/1.20  ----------------------
% 1.75/1.20  #Subsume      : 7
% 1.75/1.20  #Demod        : 4
% 1.75/1.20  #Tautology    : 17
% 1.75/1.20  #SimpNegUnit  : 10
% 1.75/1.20  #BackRed      : 3
% 1.75/1.20  
% 1.75/1.20  #Partial instantiations: 0
% 1.75/1.20  #Strategies tried      : 1
% 1.75/1.20  
% 1.75/1.20  Timing (in seconds)
% 1.75/1.20  ----------------------
% 1.75/1.20  Preprocessing        : 0.28
% 1.75/1.20  Parsing              : 0.15
% 1.75/1.20  CNF conversion       : 0.02
% 1.75/1.20  Main loop            : 0.12
% 1.75/1.20  Inferencing          : 0.05
% 1.75/1.20  Reduction            : 0.04
% 1.75/1.20  Demodulation         : 0.02
% 1.75/1.20  BG Simplification    : 0.01
% 1.75/1.20  Subsumption          : 0.02
% 1.75/1.20  Abstraction          : 0.01
% 1.75/1.20  MUC search           : 0.00
% 1.75/1.20  Cooper               : 0.00
% 1.75/1.20  Total                : 0.42
% 1.75/1.20  Index Insertion      : 0.00
% 1.75/1.20  Index Deletion       : 0.00
% 1.75/1.20  Index Matching       : 0.00
% 1.75/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
