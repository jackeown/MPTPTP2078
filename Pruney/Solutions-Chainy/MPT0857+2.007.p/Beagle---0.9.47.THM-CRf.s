%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  77 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_118,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_76] : r1_tarski(A_76,A_76) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | ~ r1_tarski(k1_tarski(A_16),B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(k1_mcart_1(A_63),B_64)
      | ~ r2_hidden(A_63,k2_zfmisc_1(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_89])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_94])).

tff(c_100,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_277,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden(A_118,k4_xboole_0(B_119,k1_tarski(C_120)))
      | C_120 = A_118
      | ~ r2_hidden(A_118,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_tarski(A_16),B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_150,plain,(
    ! [A_86,C_87,B_88] :
      ( r2_hidden(k2_mcart_1(A_86),C_87)
      | ~ r2_hidden(A_86,k2_zfmisc_1(B_88,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_158,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_205,plain,(
    ! [B_96] :
      ( r2_hidden(k2_mcart_1('#skF_3'),B_96)
      | ~ r1_tarski(k1_tarski('#skF_5'),B_96) ) ),
    inference(resolution,[status(thm)],[c_157,c_158])).

tff(c_30,plain,(
    ! [C_38,B_37] : ~ r2_hidden(C_38,k4_xboole_0(B_37,k1_tarski(C_38))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_238,plain,(
    ! [B_100] : ~ r1_tarski(k1_tarski('#skF_5'),k4_xboole_0(B_100,k1_tarski(k2_mcart_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_205,c_30])).

tff(c_242,plain,(
    ! [B_100] : ~ r2_hidden('#skF_5',k4_xboole_0(B_100,k1_tarski(k2_mcart_1('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_18,c_238])).

tff(c_281,plain,(
    ! [B_119] :
      ( k2_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_119) ) ),
    inference(resolution,[status(thm)],[c_277,c_242])).

tff(c_303,plain,(
    ! [B_121] : ~ r2_hidden('#skF_5',B_121) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_281])).

tff(c_316,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_129,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n022.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:50:25 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.34  %$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.29/1.34  
% 2.29/1.34  %Foreground sorts:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Background operators:
% 2.29/1.34  
% 2.29/1.34  
% 2.29/1.34  %Foreground operators:
% 2.29/1.34  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 2.29/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.29/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.29/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.34  
% 2.29/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.35  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.29/1.35  tff(f_89, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.29/1.35  tff(f_82, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.29/1.35  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.29/1.35  tff(c_118, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), A_74) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.35  tff(c_124, plain, (![A_76]: (r1_tarski(A_76, A_76))), inference(resolution, [status(thm)], [c_118, c_4])).
% 2.29/1.35  tff(c_16, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | ~r1_tarski(k1_tarski(A_16), B_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.35  tff(c_129, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(resolution, [status(thm)], [c_124, c_16])).
% 2.29/1.35  tff(c_38, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.29/1.35  tff(c_52, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 2.29/1.35  tff(c_40, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.29/1.35  tff(c_89, plain, (![A_63, B_64, C_65]: (r2_hidden(k1_mcart_1(A_63), B_64) | ~r2_hidden(A_63, k2_zfmisc_1(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.35  tff(c_94, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_40, c_89])).
% 2.29/1.35  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_94])).
% 2.29/1.35  tff(c_100, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 2.29/1.35  tff(c_277, plain, (![A_118, B_119, C_120]: (r2_hidden(A_118, k4_xboole_0(B_119, k1_tarski(C_120))) | C_120=A_118 | ~r2_hidden(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.35  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.35  tff(c_150, plain, (![A_86, C_87, B_88]: (r2_hidden(k2_mcart_1(A_86), C_87) | ~r2_hidden(A_86, k2_zfmisc_1(B_88, C_87)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.35  tff(c_157, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_150])).
% 2.29/1.35  tff(c_158, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.35  tff(c_205, plain, (![B_96]: (r2_hidden(k2_mcart_1('#skF_3'), B_96) | ~r1_tarski(k1_tarski('#skF_5'), B_96))), inference(resolution, [status(thm)], [c_157, c_158])).
% 2.29/1.35  tff(c_30, plain, (![C_38, B_37]: (~r2_hidden(C_38, k4_xboole_0(B_37, k1_tarski(C_38))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.35  tff(c_238, plain, (![B_100]: (~r1_tarski(k1_tarski('#skF_5'), k4_xboole_0(B_100, k1_tarski(k2_mcart_1('#skF_3')))))), inference(resolution, [status(thm)], [c_205, c_30])).
% 2.29/1.35  tff(c_242, plain, (![B_100]: (~r2_hidden('#skF_5', k4_xboole_0(B_100, k1_tarski(k2_mcart_1('#skF_3')))))), inference(resolution, [status(thm)], [c_18, c_238])).
% 2.29/1.35  tff(c_281, plain, (![B_119]: (k2_mcart_1('#skF_3')='#skF_5' | ~r2_hidden('#skF_5', B_119))), inference(resolution, [status(thm)], [c_277, c_242])).
% 2.29/1.35  tff(c_303, plain, (![B_121]: (~r2_hidden('#skF_5', B_121))), inference(negUnitSimplification, [status(thm)], [c_100, c_281])).
% 2.29/1.35  tff(c_316, plain, $false, inference(resolution, [status(thm)], [c_129, c_303])).
% 2.29/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  Inference rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Ref     : 0
% 2.29/1.35  #Sup     : 56
% 2.29/1.35  #Fact    : 0
% 2.29/1.35  #Define  : 0
% 2.29/1.35  #Split   : 1
% 2.29/1.35  #Chain   : 0
% 2.29/1.35  #Close   : 0
% 2.29/1.35  
% 2.29/1.35  Ordering : KBO
% 2.29/1.35  
% 2.29/1.35  Simplification rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Subsume      : 4
% 2.29/1.35  #Demod        : 3
% 2.29/1.35  #Tautology    : 18
% 2.29/1.35  #SimpNegUnit  : 2
% 2.29/1.35  #BackRed      : 0
% 2.29/1.35  
% 2.29/1.35  #Partial instantiations: 0
% 2.29/1.35  #Strategies tried      : 1
% 2.29/1.35  
% 2.29/1.35  Timing (in seconds)
% 2.29/1.35  ----------------------
% 2.29/1.35  Preprocessing        : 0.41
% 2.29/1.35  Parsing              : 0.24
% 2.29/1.35  CNF conversion       : 0.02
% 2.29/1.35  Main loop            : 0.22
% 2.29/1.35  Inferencing          : 0.09
% 2.29/1.35  Reduction            : 0.06
% 2.29/1.35  Demodulation         : 0.04
% 2.29/1.35  BG Simplification    : 0.01
% 2.29/1.35  Subsumption          : 0.04
% 2.29/1.35  Abstraction          : 0.01
% 2.29/1.35  MUC search           : 0.00
% 2.29/1.35  Cooper               : 0.00
% 2.29/1.35  Total                : 0.65
% 2.29/1.35  Index Insertion      : 0.00
% 2.29/1.35  Index Deletion       : 0.00
% 2.29/1.35  Index Matching       : 0.00
% 2.29/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
