%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:14 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  90 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_15,C_16,B_17] :
      ( r2_xboole_0(A_15,C_16)
      | ~ r1_tarski(B_17,C_16)
      | ~ r2_xboole_0(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    ! [A_18] :
      ( r2_xboole_0(A_18,'#skF_3')
      | ~ r2_xboole_0(A_18,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_35])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,'#skF_3')
      | ~ r2_xboole_0(A_19,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_6])).

tff(c_63,plain,(
    ! [A_20] :
      ( r1_tarski(A_20,'#skF_3')
      | A_20 = '#skF_1'
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_12,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,
    ( k1_setfam_1('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_12])).

tff(c_76,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_84,plain,(
    k1_setfam_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_86,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_12])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  %$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.12  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.63/1.12  
% 1.74/1.13  tff(f_49, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.74/1.13  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.74/1.13  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.74/1.13  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.74/1.13  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.13  tff(c_16, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.13  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.13  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.13  tff(c_35, plain, (![A_15, C_16, B_17]: (r2_xboole_0(A_15, C_16) | ~r1_tarski(B_17, C_16) | ~r2_xboole_0(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.74/1.13  tff(c_42, plain, (![A_18]: (r2_xboole_0(A_18, '#skF_3') | ~r2_xboole_0(A_18, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_35])).
% 1.74/1.13  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.13  tff(c_57, plain, (![A_19]: (r1_tarski(A_19, '#skF_3') | ~r2_xboole_0(A_19, '#skF_1'))), inference(resolution, [status(thm)], [c_42, c_6])).
% 1.74/1.13  tff(c_63, plain, (![A_20]: (r1_tarski(A_20, '#skF_3') | A_20='#skF_1' | ~r1_tarski(A_20, '#skF_1'))), inference(resolution, [status(thm)], [c_2, c_57])).
% 1.74/1.13  tff(c_12, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.13  tff(c_70, plain, (k1_setfam_1('#skF_2')='#skF_1' | ~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_63, c_12])).
% 1.74/1.13  tff(c_76, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 1.74/1.13  tff(c_79, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_76])).
% 1.74/1.13  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 1.74/1.13  tff(c_84, plain, (k1_setfam_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_70])).
% 1.74/1.13  tff(c_86, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_12])).
% 1.74/1.13  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_86])).
% 1.74/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.13  
% 1.74/1.13  Inference rules
% 1.74/1.13  ----------------------
% 1.74/1.13  #Ref     : 0
% 1.74/1.13  #Sup     : 13
% 1.74/1.13  #Fact    : 0
% 1.74/1.13  #Define  : 0
% 1.74/1.13  #Split   : 2
% 1.74/1.13  #Chain   : 0
% 1.74/1.13  #Close   : 0
% 1.74/1.13  
% 1.74/1.13  Ordering : KBO
% 1.74/1.13  
% 1.74/1.13  Simplification rules
% 1.74/1.13  ----------------------
% 1.74/1.13  #Subsume      : 0
% 1.74/1.13  #Demod        : 3
% 1.74/1.13  #Tautology    : 2
% 1.74/1.13  #SimpNegUnit  : 0
% 1.74/1.13  #BackRed      : 1
% 1.74/1.13  
% 1.74/1.13  #Partial instantiations: 0
% 1.74/1.13  #Strategies tried      : 1
% 1.74/1.13  
% 1.74/1.13  Timing (in seconds)
% 1.74/1.13  ----------------------
% 1.74/1.13  Preprocessing        : 0.25
% 1.74/1.13  Parsing              : 0.14
% 1.74/1.13  CNF conversion       : 0.02
% 1.74/1.14  Main loop            : 0.13
% 1.74/1.14  Inferencing          : 0.05
% 1.74/1.14  Reduction            : 0.03
% 1.74/1.14  Demodulation         : 0.02
% 1.74/1.14  BG Simplification    : 0.01
% 1.74/1.14  Subsumption          : 0.03
% 1.74/1.14  Abstraction          : 0.00
% 1.74/1.14  MUC search           : 0.00
% 1.74/1.14  Cooper               : 0.00
% 1.74/1.14  Total                : 0.41
% 1.74/1.14  Index Insertion      : 0.00
% 1.74/1.14  Index Deletion       : 0.00
% 1.74/1.14  Index Matching       : 0.00
% 1.74/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
