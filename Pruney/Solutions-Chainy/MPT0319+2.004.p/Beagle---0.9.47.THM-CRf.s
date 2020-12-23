%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:11 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   43 (  73 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 ( 124 expanded)
%              Number of equality atoms :   10 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( A != B
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),D))
          & r1_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(D,k1_tarski(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_154,plain,(
    ! [C_57,D_58,A_59,B_60] :
      ( ~ r1_xboole_0(C_57,D_58)
      | r1_xboole_0(k2_zfmisc_1(A_59,C_57),k2_zfmisc_1(B_60,D_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( ~ r1_xboole_0(A_41,B_42)
      | r1_xboole_0(k2_zfmisc_1(A_41,C_43),k2_zfmisc_1(B_42,D_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_5')))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_95,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_89,c_80])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_27,A_6] :
      ( '#skF_1'(A_27,k1_tarski(A_6)) = A_6
      | r1_xboole_0(A_27,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_58,c_8])).

tff(c_103,plain,(
    '#skF_1'(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_63,c_95])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_4'))
    | r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_6])).

tff(c_122,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_116])).

tff(c_128,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_128])).

tff(c_133,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_6',k1_tarski('#skF_4')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_160,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_154,c_133])).

tff(c_168,plain,(
    '#skF_1'(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_63,c_160])).

tff(c_173,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_4'))
    | r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_6])).

tff(c_179,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_173])).

tff(c_185,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_179,c_8])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.24  
% 1.89/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.24  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 1.89/1.24  
% 1.89/1.24  %Foreground sorts:
% 1.89/1.24  
% 1.89/1.24  
% 1.89/1.24  %Background operators:
% 1.89/1.24  
% 1.89/1.24  
% 1.89/1.24  %Foreground operators:
% 1.89/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.24  tff('#skF_7', type, '#skF_7': $i).
% 1.89/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.89/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.24  
% 1.94/1.25  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (~(A = B) => (r1_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), D)) & r1_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(D, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_zfmisc_1)).
% 1.94/1.25  tff(f_62, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.94/1.25  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.94/1.25  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.94/1.25  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.25  tff(c_154, plain, (![C_57, D_58, A_59, B_60]: (~r1_xboole_0(C_57, D_58) | r1_xboole_0(k2_zfmisc_1(A_59, C_57), k2_zfmisc_1(B_60, D_58)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.25  tff(c_89, plain, (![A_41, B_42, C_43, D_44]: (~r1_xboole_0(A_41, B_42) | r1_xboole_0(k2_zfmisc_1(A_41, C_43), k2_zfmisc_1(B_42, D_44)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.94/1.25  tff(c_30, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')), k2_zfmisc_1('#skF_7', k1_tarski('#skF_5'))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.94/1.25  tff(c_80, plain, (~r1_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_30])).
% 1.94/1.25  tff(c_95, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_89, c_80])).
% 1.94/1.25  tff(c_58, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.25  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.94/1.25  tff(c_63, plain, (![A_27, A_6]: ('#skF_1'(A_27, k1_tarski(A_6))=A_6 | r1_xboole_0(A_27, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_58, c_8])).
% 1.94/1.25  tff(c_103, plain, ('#skF_1'(k1_tarski('#skF_4'), k1_tarski('#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_63, c_95])).
% 1.94/1.25  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.25  tff(c_116, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4')) | r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_6])).
% 1.94/1.25  tff(c_122, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_95, c_116])).
% 1.94/1.25  tff(c_128, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_122, c_8])).
% 1.94/1.25  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_128])).
% 1.94/1.25  tff(c_133, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_6', k1_tarski('#skF_4')), k2_zfmisc_1('#skF_7', k1_tarski('#skF_5')))), inference(splitRight, [status(thm)], [c_30])).
% 1.94/1.25  tff(c_160, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_154, c_133])).
% 1.94/1.25  tff(c_168, plain, ('#skF_1'(k1_tarski('#skF_4'), k1_tarski('#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_63, c_160])).
% 1.94/1.25  tff(c_173, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4')) | r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_6])).
% 1.94/1.25  tff(c_179, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_173])).
% 1.94/1.25  tff(c_185, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_179, c_8])).
% 1.94/1.25  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_185])).
% 1.94/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  Inference rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Ref     : 0
% 1.94/1.25  #Sup     : 36
% 1.94/1.25  #Fact    : 0
% 1.94/1.25  #Define  : 0
% 1.94/1.25  #Split   : 1
% 1.94/1.25  #Chain   : 0
% 1.94/1.25  #Close   : 0
% 1.94/1.25  
% 1.94/1.25  Ordering : KBO
% 1.94/1.25  
% 1.94/1.25  Simplification rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Subsume      : 0
% 1.94/1.25  #Demod        : 2
% 1.94/1.25  #Tautology    : 13
% 1.94/1.25  #SimpNegUnit  : 6
% 1.94/1.25  #BackRed      : 0
% 1.94/1.25  
% 1.94/1.25  #Partial instantiations: 0
% 1.94/1.25  #Strategies tried      : 1
% 1.94/1.25  
% 1.94/1.25  Timing (in seconds)
% 1.94/1.25  ----------------------
% 1.94/1.25  Preprocessing        : 0.30
% 1.94/1.26  Parsing              : 0.16
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.15
% 1.94/1.26  Inferencing          : 0.06
% 1.94/1.26  Reduction            : 0.04
% 1.94/1.26  Demodulation         : 0.03
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.03
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.48
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
