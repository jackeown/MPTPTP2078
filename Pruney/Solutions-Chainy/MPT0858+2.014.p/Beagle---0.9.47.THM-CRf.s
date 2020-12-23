%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(c_30,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k1_mcart_1(A_51),B_52)
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_52,k1_tarski(C_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_28,plain,(
    ! [A_36,B_37] : k2_mcart_1(k4_tarski(A_36,B_37)) = B_37 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_94,plain,(
    ! [C_58,B_59,D_60] :
      ( r2_hidden(k4_tarski(C_58,B_59),k2_zfmisc_1(k1_tarski(C_58),D_60))
      | ~ r2_hidden(B_59,D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_33,C_35,B_34] :
      ( k2_mcart_1(A_33) = C_35
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_34,k1_tarski(C_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [C_58,B_59,C_35] :
      ( k2_mcart_1(k4_tarski(C_58,B_59)) = C_35
      | ~ r2_hidden(B_59,k1_tarski(C_35)) ) ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_112,plain,(
    ! [C_61,B_62] :
      ( C_61 = B_62
      | ~ r2_hidden(B_62,k1_tarski(C_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_105])).

tff(c_115,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_92,c_112])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_115])).

tff(c_120,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_135,plain,(
    ! [A_65,C_66,B_67] :
      ( k2_mcart_1(A_65) = C_66
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_67,k1_tarski(C_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.18  
% 1.97/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.18  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.18  
% 1.97/1.18  %Foreground sorts:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Background operators:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Foreground operators:
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.97/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.97/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  
% 1.97/1.19  tff(f_62, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.97/1.19  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.97/1.19  tff(f_55, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.97/1.19  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 1.97/1.19  tff(c_30, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.19  tff(c_60, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 1.97/1.19  tff(c_32, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.19  tff(c_88, plain, (![A_51, B_52, C_53]: (r2_hidden(k1_mcart_1(A_51), B_52) | ~r2_hidden(A_51, k2_zfmisc_1(B_52, k1_tarski(C_53))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.19  tff(c_92, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_88])).
% 1.97/1.19  tff(c_28, plain, (![A_36, B_37]: (k2_mcart_1(k4_tarski(A_36, B_37))=B_37)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.19  tff(c_94, plain, (![C_58, B_59, D_60]: (r2_hidden(k4_tarski(C_58, B_59), k2_zfmisc_1(k1_tarski(C_58), D_60)) | ~r2_hidden(B_59, D_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.19  tff(c_22, plain, (![A_33, C_35, B_34]: (k2_mcart_1(A_33)=C_35 | ~r2_hidden(A_33, k2_zfmisc_1(B_34, k1_tarski(C_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.19  tff(c_105, plain, (![C_58, B_59, C_35]: (k2_mcart_1(k4_tarski(C_58, B_59))=C_35 | ~r2_hidden(B_59, k1_tarski(C_35)))), inference(resolution, [status(thm)], [c_94, c_22])).
% 1.97/1.19  tff(c_112, plain, (![C_61, B_62]: (C_61=B_62 | ~r2_hidden(B_62, k1_tarski(C_61)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_105])).
% 1.97/1.19  tff(c_115, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_92, c_112])).
% 1.97/1.19  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_115])).
% 1.97/1.19  tff(c_120, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 1.97/1.19  tff(c_135, plain, (![A_65, C_66, B_67]: (k2_mcart_1(A_65)=C_66 | ~r2_hidden(A_65, k2_zfmisc_1(B_67, k1_tarski(C_66))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.19  tff(c_138, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_135])).
% 1.97/1.19  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_138])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 23
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 1
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 0
% 1.97/1.19  #Demod        : 2
% 1.97/1.19  #Tautology    : 17
% 1.97/1.19  #SimpNegUnit  : 2
% 1.97/1.19  #BackRed      : 0
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.20  Preprocessing        : 0.32
% 1.97/1.20  Parsing              : 0.16
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.12
% 1.97/1.20  Inferencing          : 0.04
% 1.97/1.20  Reduction            : 0.04
% 1.97/1.20  Demodulation         : 0.03
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.47
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
