%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   42 (  76 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [B_38,C_39] :
      ( k4_xboole_0(k2_tarski(B_38,B_38),C_39) = k1_tarski(B_38)
      | r2_hidden(B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [B_58,C_59] :
      ( k4_xboole_0(k1_tarski(B_58),C_59) = k1_tarski(B_58)
      | r2_hidden(B_58,C_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_164,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_120])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_164])).

tff(c_173,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_174,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_258,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_38])).

tff(c_235,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,C_68)
      | k4_xboole_0(k2_tarski(A_67,B_69),C_68) != k1_tarski(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_238,plain,(
    ! [A_7,C_68] :
      ( ~ r2_hidden(A_7,C_68)
      | k4_xboole_0(k1_tarski(A_7),C_68) != k1_tarski(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_235])).

tff(c_262,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_238])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_262])).

tff(c_275,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_276,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_360,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_40])).

tff(c_375,plain,(
    ! [A_93,C_94,B_95] :
      ( ~ r2_hidden(A_93,C_94)
      | k4_xboole_0(k2_tarski(A_93,B_95),C_94) != k1_tarski(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_379,plain,(
    ! [A_96,C_97] :
      ( ~ r2_hidden(A_96,C_97)
      | k4_xboole_0(k1_tarski(A_96),C_97) != k1_tarski(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_375])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_379])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:57:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  
% 2.22/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.27  
% 2.22/1.27  %Foreground sorts:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Background operators:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Foreground operators:
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.27  
% 2.22/1.28  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.22/1.28  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.28  tff(f_61, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.22/1.28  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_84, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 2.22/1.28  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.28  tff(c_30, plain, (![B_38, C_39]: (k4_xboole_0(k2_tarski(B_38, B_38), C_39)=k1_tarski(B_38) | r2_hidden(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.28  tff(c_158, plain, (![B_58, C_59]: (k4_xboole_0(k1_tarski(B_58), C_59)=k1_tarski(B_58) | r2_hidden(B_58, C_59))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 2.22/1.28  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_120, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.22/1.28  tff(c_164, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_158, c_120])).
% 2.22/1.28  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_164])).
% 2.22/1.28  tff(c_173, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.22/1.28  tff(c_174, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.22/1.28  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_258, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_38])).
% 2.22/1.28  tff(c_235, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, C_68) | k4_xboole_0(k2_tarski(A_67, B_69), C_68)!=k1_tarski(A_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.28  tff(c_238, plain, (![A_7, C_68]: (~r2_hidden(A_7, C_68) | k4_xboole_0(k1_tarski(A_7), C_68)!=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_235])).
% 2.22/1.28  tff(c_262, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_258, c_238])).
% 2.22/1.28  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_262])).
% 2.22/1.28  tff(c_275, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.22/1.28  tff(c_276, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.22/1.28  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.28  tff(c_360, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_40])).
% 2.22/1.28  tff(c_375, plain, (![A_93, C_94, B_95]: (~r2_hidden(A_93, C_94) | k4_xboole_0(k2_tarski(A_93, B_95), C_94)!=k1_tarski(A_93))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.28  tff(c_379, plain, (![A_96, C_97]: (~r2_hidden(A_96, C_97) | k4_xboole_0(k1_tarski(A_96), C_97)!=k1_tarski(A_96))), inference(superposition, [status(thm), theory('equality')], [c_10, c_375])).
% 2.22/1.28  tff(c_382, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_360, c_379])).
% 2.22/1.28  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_275, c_382])).
% 2.22/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.28  
% 2.22/1.28  Inference rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Ref     : 0
% 2.22/1.28  #Sup     : 78
% 2.22/1.28  #Fact    : 0
% 2.22/1.28  #Define  : 0
% 2.22/1.28  #Split   : 2
% 2.22/1.28  #Chain   : 0
% 2.22/1.28  #Close   : 0
% 2.22/1.28  
% 2.22/1.28  Ordering : KBO
% 2.22/1.28  
% 2.22/1.28  Simplification rules
% 2.22/1.28  ----------------------
% 2.22/1.28  #Subsume      : 4
% 2.22/1.28  #Demod        : 17
% 2.22/1.28  #Tautology    : 65
% 2.22/1.28  #SimpNegUnit  : 3
% 2.22/1.28  #BackRed      : 0
% 2.22/1.28  
% 2.22/1.28  #Partial instantiations: 0
% 2.22/1.28  #Strategies tried      : 1
% 2.22/1.28  
% 2.22/1.28  Timing (in seconds)
% 2.22/1.28  ----------------------
% 2.22/1.28  Preprocessing        : 0.33
% 2.22/1.28  Parsing              : 0.17
% 2.22/1.28  CNF conversion       : 0.02
% 2.22/1.28  Main loop            : 0.20
% 2.22/1.28  Inferencing          : 0.08
% 2.22/1.28  Reduction            : 0.06
% 2.22/1.28  Demodulation         : 0.05
% 2.22/1.28  BG Simplification    : 0.02
% 2.22/1.28  Subsumption          : 0.03
% 2.22/1.28  Abstraction          : 0.02
% 2.22/1.28  MUC search           : 0.00
% 2.22/1.28  Cooper               : 0.00
% 2.22/1.28  Total                : 0.56
% 2.22/1.28  Index Insertion      : 0.00
% 2.22/1.28  Index Deletion       : 0.00
% 2.22/1.28  Index Matching       : 0.00
% 2.22/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
