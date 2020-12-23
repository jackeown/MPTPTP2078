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
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
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
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

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
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    ! [A_55,C_56,B_57] :
      ( r2_hidden(k2_mcart_1(A_55),C_56)
      | ~ r2_hidden(A_55,k2_zfmisc_1(B_57,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_140,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_137])).

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

tff(c_143,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_140,c_106])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_143])).

tff(c_149,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_50])).

tff(c_148,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_190,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(k1_mcart_1(A_77),B_78)
      | ~ r2_hidden(A_77,k2_zfmisc_1(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_190])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_251,plain,(
    ! [E_96,C_97,B_98,A_99] :
      ( E_96 = C_97
      | E_96 = B_98
      | E_96 = A_99
      | ~ r2_hidden(E_96,k1_enumset1(A_99,B_98,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_270,plain,(
    ! [E_100,B_101,A_102] :
      ( E_100 = B_101
      | E_100 = A_102
      | E_100 = A_102
      | ~ r2_hidden(E_100,k2_tarski(A_102,B_101)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_251])).

tff(c_273,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_270])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_156,c_148,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.08/1.30  
% 2.08/1.31  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.08/1.31  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.08/1.31  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.31  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.08/1.31  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.08/1.31  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.08/1.31  tff(c_48, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.31  tff(c_60, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 2.08/1.31  tff(c_46, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.31  tff(c_137, plain, (![A_55, C_56, B_57]: (r2_hidden(k2_mcart_1(A_55), C_56) | ~r2_hidden(A_55, k2_zfmisc_1(B_57, C_56)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.31  tff(c_140, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_137])).
% 2.08/1.31  tff(c_96, plain, (![A_42, B_43]: (k4_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k1_tarski(A_42) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.08/1.31  tff(c_38, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.31  tff(c_106, plain, (![B_43, A_42]: (~r2_hidden(B_43, k1_tarski(A_42)) | B_43=A_42)), inference(superposition, [status(thm), theory('equality')], [c_96, c_38])).
% 2.08/1.31  tff(c_143, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_140, c_106])).
% 2.08/1.31  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_143])).
% 2.08/1.31  tff(c_149, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 2.08/1.31  tff(c_50, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.31  tff(c_156, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_50])).
% 2.08/1.31  tff(c_148, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 2.08/1.31  tff(c_190, plain, (![A_77, B_78, C_79]: (r2_hidden(k1_mcart_1(A_77), B_78) | ~r2_hidden(A_77, k2_zfmisc_1(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.31  tff(c_193, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_190])).
% 2.08/1.31  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.08/1.31  tff(c_251, plain, (![E_96, C_97, B_98, A_99]: (E_96=C_97 | E_96=B_98 | E_96=A_99 | ~r2_hidden(E_96, k1_enumset1(A_99, B_98, C_97)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.31  tff(c_270, plain, (![E_100, B_101, A_102]: (E_100=B_101 | E_100=A_102 | E_100=A_102 | ~r2_hidden(E_100, k2_tarski(A_102, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_251])).
% 2.08/1.31  tff(c_273, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_193, c_270])).
% 2.08/1.31  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_156, c_148, c_273])).
% 2.08/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  Inference rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Ref     : 0
% 2.08/1.31  #Sup     : 50
% 2.08/1.31  #Fact    : 0
% 2.08/1.31  #Define  : 0
% 2.08/1.31  #Split   : 1
% 2.08/1.31  #Chain   : 0
% 2.08/1.31  #Close   : 0
% 2.08/1.31  
% 2.08/1.31  Ordering : KBO
% 2.08/1.31  
% 2.08/1.31  Simplification rules
% 2.08/1.31  ----------------------
% 2.08/1.31  #Subsume      : 1
% 2.08/1.31  #Demod        : 7
% 2.08/1.31  #Tautology    : 33
% 2.08/1.31  #SimpNegUnit  : 2
% 2.08/1.31  #BackRed      : 0
% 2.08/1.31  
% 2.08/1.31  #Partial instantiations: 0
% 2.08/1.31  #Strategies tried      : 1
% 2.08/1.31  
% 2.08/1.31  Timing (in seconds)
% 2.08/1.31  ----------------------
% 2.08/1.31  Preprocessing        : 0.31
% 2.08/1.31  Parsing              : 0.17
% 2.08/1.31  CNF conversion       : 0.02
% 2.08/1.32  Main loop            : 0.19
% 2.08/1.32  Inferencing          : 0.07
% 2.08/1.32  Reduction            : 0.06
% 2.08/1.32  Demodulation         : 0.04
% 2.08/1.32  BG Simplification    : 0.01
% 2.08/1.32  Subsumption          : 0.03
% 2.08/1.32  Abstraction          : 0.01
% 2.08/1.32  MUC search           : 0.00
% 2.08/1.32  Cooper               : 0.00
% 2.08/1.32  Total                : 0.53
% 2.08/1.32  Index Insertion      : 0.00
% 2.08/1.32  Index Deletion       : 0.00
% 2.08/1.32  Index Matching       : 0.00
% 2.08/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
