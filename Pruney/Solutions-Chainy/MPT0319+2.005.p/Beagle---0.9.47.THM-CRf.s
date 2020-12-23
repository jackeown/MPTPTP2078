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
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  70 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_xboole_0(k2_tarski(A_69,C_70),B_71)
      | r2_hidden(C_70,B_71)
      | r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(k1_tarski(A_72),B_73)
      | r2_hidden(A_72,B_73)
      | r2_hidden(A_72,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_28,plain,(
    ! [C_36,D_37,A_34,B_35] :
      ( ~ r1_xboole_0(C_36,D_37)
      | r1_xboole_0(k2_zfmisc_1(A_34,C_36),k2_zfmisc_1(B_35,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(k2_tarski(A_62,C_63),B_64)
      | r2_hidden(C_63,B_64)
      | r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(k1_tarski(A_65),B_66)
      | r2_hidden(A_65,B_66)
      | r2_hidden(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_30,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( ~ r1_xboole_0(A_34,B_35)
      | r1_xboole_0(k2_zfmisc_1(A_34,C_36),k2_zfmisc_1(B_35,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_5'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_90,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_99,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_95,c_90])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_103])).

tff(c_108,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_5',k1_tarski('#skF_3')),k2_zfmisc_1('#skF_6',k1_tarski('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_116,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_126,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_122,c_116])).

tff(c_129,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.19  
% 1.91/1.20  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.91/1.20  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.20  tff(f_62, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.91/1.20  tff(f_52, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.91/1.20  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.91/1.20  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.20  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.20  tff(c_118, plain, (![A_69, C_70, B_71]: (r1_xboole_0(k2_tarski(A_69, C_70), B_71) | r2_hidden(C_70, B_71) | r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.20  tff(c_122, plain, (![A_72, B_73]: (r1_xboole_0(k1_tarski(A_72), B_73) | r2_hidden(A_72, B_73) | r2_hidden(A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 1.91/1.20  tff(c_28, plain, (![C_36, D_37, A_34, B_35]: (~r1_xboole_0(C_36, D_37) | r1_xboole_0(k2_zfmisc_1(A_34, C_36), k2_zfmisc_1(B_35, D_37)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.20  tff(c_91, plain, (![A_62, C_63, B_64]: (r1_xboole_0(k2_tarski(A_62, C_63), B_64) | r2_hidden(C_63, B_64) | r2_hidden(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.20  tff(c_95, plain, (![A_65, B_66]: (r1_xboole_0(k1_tarski(A_65), B_66) | r2_hidden(A_65, B_66) | r2_hidden(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_91])).
% 1.91/1.20  tff(c_30, plain, (![A_34, B_35, C_36, D_37]: (~r1_xboole_0(A_34, B_35) | r1_xboole_0(k2_zfmisc_1(A_34, C_36), k2_zfmisc_1(B_35, D_37)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.20  tff(c_34, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.91/1.20  tff(c_82, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_5'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_34])).
% 1.91/1.20  tff(c_90, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_82])).
% 1.91/1.20  tff(c_99, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_95, c_90])).
% 1.91/1.20  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.20  tff(c_103, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_99, c_2])).
% 1.91/1.20  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_103])).
% 1.91/1.20  tff(c_108, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_5', k1_tarski('#skF_3')), k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_34])).
% 1.91/1.20  tff(c_116, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_108])).
% 1.91/1.20  tff(c_126, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_122, c_116])).
% 1.91/1.20  tff(c_129, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_126, c_2])).
% 1.91/1.20  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_129])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 19
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 1
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 0
% 1.91/1.20  #Demod        : 0
% 1.91/1.20  #Tautology    : 9
% 1.91/1.20  #SimpNegUnit  : 2
% 1.91/1.20  #BackRed      : 0
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 2.01/1.20  Preprocessing        : 0.31
% 2.01/1.20  Parsing              : 0.16
% 2.01/1.20  CNF conversion       : 0.02
% 2.01/1.20  Main loop            : 0.13
% 2.01/1.20  Inferencing          : 0.05
% 2.01/1.20  Reduction            : 0.04
% 2.01/1.20  Demodulation         : 0.02
% 2.01/1.20  BG Simplification    : 0.01
% 2.01/1.20  Subsumption          : 0.03
% 2.01/1.20  Abstraction          : 0.01
% 2.01/1.20  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.47
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
