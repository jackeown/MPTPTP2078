%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    4
%              Number of atoms          :   52 (  94 expanded)
%              Number of equality atoms :   32 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_48,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_129,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden(k1_mcart_1(A_49),B_50)
      | ~ r2_hidden(A_49,k2_zfmisc_1(B_50,C_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_132,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_129])).

tff(c_96,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) = k1_tarski(A_42)
      | B_43 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [B_43,A_42] :
      ( ~ r2_hidden(B_43,k1_tarski(A_42))
      | B_43 = A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_135,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_132,c_106])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_135])).

tff(c_141,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_151,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_50])).

tff(c_140,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_212,plain,(
    ! [A_78,C_79,B_80] :
      ( r2_hidden(k2_mcart_1(A_78),C_79)
      | ~ r2_hidden(A_78,k2_zfmisc_1(B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_215,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_212])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_243,plain,(
    ! [E_90,C_91,B_92,A_93] :
      ( E_90 = C_91
      | E_90 = B_92
      | E_90 = A_93
      | ~ r2_hidden(E_90,k1_enumset1(A_93,B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_262,plain,(
    ! [E_94,B_95,A_96] :
      ( E_94 = B_95
      | E_94 = A_96
      | E_94 = A_96
      | ~ r2_hidden(E_94,k2_tarski(A_96,B_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_243])).

tff(c_265,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_215,c_262])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_151,c_140,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.48  
% 2.41/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.48  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.41/1.48  
% 2.41/1.48  %Foreground sorts:
% 2.41/1.48  
% 2.41/1.48  
% 2.41/1.48  %Background operators:
% 2.41/1.48  
% 2.41/1.48  
% 2.41/1.48  %Foreground operators:
% 2.41/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.41/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.48  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.41/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.48  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.41/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.41/1.48  
% 2.41/1.49  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.41/1.49  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.41/1.49  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.41/1.49  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.41/1.49  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.41/1.49  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.41/1.49  tff(c_48, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.49  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.41/1.49  tff(c_46, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.49  tff(c_129, plain, (![A_49, B_50, C_51]: (r2_hidden(k1_mcart_1(A_49), B_50) | ~r2_hidden(A_49, k2_zfmisc_1(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.41/1.49  tff(c_132, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_129])).
% 2.41/1.49  tff(c_96, plain, (![A_42, B_43]: (k4_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k1_tarski(A_42) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.49  tff(c_38, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.49  tff(c_106, plain, (![B_43, A_42]: (~r2_hidden(B_43, k1_tarski(A_42)) | B_43=A_42)), inference(superposition, [status(thm), theory('equality')], [c_96, c_38])).
% 2.41/1.49  tff(c_135, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_132, c_106])).
% 2.41/1.49  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_135])).
% 2.41/1.49  tff(c_141, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.41/1.49  tff(c_50, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.41/1.49  tff(c_151, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_50])).
% 2.41/1.49  tff(c_140, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 2.41/1.49  tff(c_212, plain, (![A_78, C_79, B_80]: (r2_hidden(k2_mcart_1(A_78), C_79) | ~r2_hidden(A_78, k2_zfmisc_1(B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.41/1.49  tff(c_215, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_212])).
% 2.41/1.49  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.41/1.49  tff(c_243, plain, (![E_90, C_91, B_92, A_93]: (E_90=C_91 | E_90=B_92 | E_90=A_93 | ~r2_hidden(E_90, k1_enumset1(A_93, B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.49  tff(c_262, plain, (![E_94, B_95, A_96]: (E_94=B_95 | E_94=A_96 | E_94=A_96 | ~r2_hidden(E_94, k2_tarski(A_96, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_243])).
% 2.41/1.49  tff(c_265, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_215, c_262])).
% 2.41/1.49  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_151, c_140, c_265])).
% 2.41/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.49  
% 2.41/1.49  Inference rules
% 2.41/1.49  ----------------------
% 2.41/1.49  #Ref     : 0
% 2.41/1.49  #Sup     : 48
% 2.41/1.49  #Fact    : 0
% 2.41/1.49  #Define  : 0
% 2.41/1.49  #Split   : 1
% 2.41/1.49  #Chain   : 0
% 2.41/1.49  #Close   : 0
% 2.41/1.49  
% 2.41/1.49  Ordering : KBO
% 2.41/1.49  
% 2.41/1.49  Simplification rules
% 2.41/1.49  ----------------------
% 2.41/1.49  #Subsume      : 1
% 2.41/1.49  #Demod        : 7
% 2.41/1.49  #Tautology    : 32
% 2.41/1.49  #SimpNegUnit  : 2
% 2.41/1.49  #BackRed      : 0
% 2.41/1.49  
% 2.41/1.49  #Partial instantiations: 0
% 2.41/1.49  #Strategies tried      : 1
% 2.41/1.49  
% 2.41/1.49  Timing (in seconds)
% 2.41/1.49  ----------------------
% 2.41/1.50  Preprocessing        : 0.40
% 2.41/1.50  Parsing              : 0.20
% 2.41/1.50  CNF conversion       : 0.03
% 2.41/1.50  Main loop            : 0.27
% 2.41/1.50  Inferencing          : 0.11
% 2.41/1.50  Reduction            : 0.08
% 2.41/1.50  Demodulation         : 0.06
% 2.41/1.50  BG Simplification    : 0.02
% 2.41/1.50  Subsumption          : 0.04
% 2.41/1.50  Abstraction          : 0.02
% 2.41/1.50  MUC search           : 0.00
% 2.41/1.50  Cooper               : 0.00
% 2.41/1.50  Total                : 0.70
% 2.41/1.50  Index Insertion      : 0.00
% 2.41/1.50  Index Deletion       : 0.00
% 2.41/1.50  Index Matching       : 0.00
% 2.41/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
