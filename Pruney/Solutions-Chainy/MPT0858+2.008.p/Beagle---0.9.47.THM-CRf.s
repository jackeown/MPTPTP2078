%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  89 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden(k1_mcart_1(A_29),B_30)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_22,plain,(
    ! [A_14,B_15] : k2_mcart_1(k4_tarski(A_14,B_15)) = B_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( r2_hidden(k4_tarski(A_40,B_41),k2_zfmisc_1(C_42,D_43))
      | ~ r2_hidden(B_41,D_43)
      | ~ r2_hidden(A_40,C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( k2_mcart_1(A_11) = C_13
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,k1_tarski(C_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [A_40,B_41,C_13,C_42] :
      ( k2_mcart_1(k4_tarski(A_40,B_41)) = C_13
      | ~ r2_hidden(B_41,k1_tarski(C_13))
      | ~ r2_hidden(A_40,C_42) ) ),
    inference(resolution,[status(thm)],[c_84,c_16])).

tff(c_104,plain,(
    ! [C_13,B_41,A_40,C_42] :
      ( C_13 = B_41
      | ~ r2_hidden(B_41,k1_tarski(C_13))
      | ~ r2_hidden(A_40,C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_96])).

tff(c_107,plain,(
    ! [A_40,C_42] : ~ r2_hidden(A_40,C_42) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_81])).

tff(c_118,plain,(
    ! [C_44,B_45] :
      ( C_44 = B_45
      | ~ r2_hidden(B_45,k1_tarski(C_44)) ) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_121,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_118])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121])).

tff(c_129,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_148,plain,(
    ! [A_51,C_52,B_53] :
      ( k2_mcart_1(A_51) = C_52
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_53,k1_tarski(C_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.17  
% 1.72/1.17  %Foreground sorts:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Background operators:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Foreground operators:
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.72/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.72/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.72/1.17  
% 1.72/1.18  tff(f_58, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.72/1.18  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.72/1.18  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.72/1.18  tff(f_35, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.72/1.18  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.72/1.18  tff(c_24, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.18  tff(c_54, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 1.72/1.18  tff(c_26, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.18  tff(c_78, plain, (![A_29, B_30, C_31]: (r2_hidden(k1_mcart_1(A_29), B_30) | ~r2_hidden(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.18  tff(c_81, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_78])).
% 1.72/1.18  tff(c_22, plain, (![A_14, B_15]: (k2_mcart_1(k4_tarski(A_14, B_15))=B_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.18  tff(c_84, plain, (![A_40, B_41, C_42, D_43]: (r2_hidden(k4_tarski(A_40, B_41), k2_zfmisc_1(C_42, D_43)) | ~r2_hidden(B_41, D_43) | ~r2_hidden(A_40, C_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.18  tff(c_16, plain, (![A_11, C_13, B_12]: (k2_mcart_1(A_11)=C_13 | ~r2_hidden(A_11, k2_zfmisc_1(B_12, k1_tarski(C_13))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.18  tff(c_96, plain, (![A_40, B_41, C_13, C_42]: (k2_mcart_1(k4_tarski(A_40, B_41))=C_13 | ~r2_hidden(B_41, k1_tarski(C_13)) | ~r2_hidden(A_40, C_42))), inference(resolution, [status(thm)], [c_84, c_16])).
% 1.72/1.18  tff(c_104, plain, (![C_13, B_41, A_40, C_42]: (C_13=B_41 | ~r2_hidden(B_41, k1_tarski(C_13)) | ~r2_hidden(A_40, C_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_96])).
% 1.72/1.18  tff(c_107, plain, (![A_40, C_42]: (~r2_hidden(A_40, C_42))), inference(splitLeft, [status(thm)], [c_104])).
% 1.72/1.18  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_81])).
% 1.72/1.18  tff(c_118, plain, (![C_44, B_45]: (C_44=B_45 | ~r2_hidden(B_45, k1_tarski(C_44)))), inference(splitRight, [status(thm)], [c_104])).
% 1.72/1.18  tff(c_121, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_81, c_118])).
% 1.72/1.18  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_121])).
% 1.72/1.18  tff(c_129, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 1.72/1.18  tff(c_148, plain, (![A_51, C_52, B_53]: (k2_mcart_1(A_51)=C_52 | ~r2_hidden(A_51, k2_zfmisc_1(B_53, k1_tarski(C_52))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.72/1.18  tff(c_151, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_148])).
% 1.72/1.18  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_151])).
% 1.72/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  Inference rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Ref     : 0
% 1.72/1.18  #Sup     : 26
% 1.72/1.18  #Fact    : 0
% 1.72/1.18  #Define  : 0
% 1.72/1.18  #Split   : 2
% 1.72/1.18  #Chain   : 0
% 1.72/1.18  #Close   : 0
% 1.72/1.18  
% 1.72/1.18  Ordering : KBO
% 1.72/1.18  
% 1.72/1.18  Simplification rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Subsume      : 7
% 1.72/1.18  #Demod        : 4
% 1.72/1.18  #Tautology    : 18
% 1.72/1.18  #SimpNegUnit  : 10
% 1.72/1.18  #BackRed      : 4
% 1.72/1.18  
% 1.72/1.18  #Partial instantiations: 0
% 1.72/1.18  #Strategies tried      : 1
% 1.72/1.18  
% 1.72/1.18  Timing (in seconds)
% 1.72/1.18  ----------------------
% 1.72/1.18  Preprocessing        : 0.28
% 1.72/1.18  Parsing              : 0.14
% 1.72/1.18  CNF conversion       : 0.02
% 1.72/1.18  Main loop            : 0.13
% 1.72/1.18  Inferencing          : 0.06
% 1.72/1.18  Reduction            : 0.04
% 1.72/1.18  Demodulation         : 0.03
% 1.72/1.18  BG Simplification    : 0.01
% 1.72/1.18  Subsumption          : 0.02
% 1.72/1.18  Abstraction          : 0.01
% 1.72/1.18  MUC search           : 0.00
% 1.72/1.18  Cooper               : 0.00
% 1.72/1.18  Total                : 0.43
% 1.72/1.18  Index Insertion      : 0.00
% 1.72/1.18  Index Deletion       : 0.00
% 1.72/1.18  Index Matching       : 0.00
% 1.72/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
