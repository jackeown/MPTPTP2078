%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:17 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_setfam_1(B_7),A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_23,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_45,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_xboole_0(A_17,C_18)
      | ~ r1_tarski(A_17,k4_xboole_0(B_19,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_20] :
      ( r1_xboole_0(A_20,'#skF_3')
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_45])).

tff(c_12,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_12])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.20  
% 1.74/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.21  
% 1.74/1.21  %Foreground sorts:
% 1.74/1.21  
% 1.74/1.21  
% 1.74/1.21  %Background operators:
% 1.74/1.21  
% 1.74/1.21  
% 1.74/1.21  %Foreground operators:
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.74/1.21  
% 1.79/1.21  tff(f_46, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.79/1.21  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.79/1.21  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.79/1.21  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.79/1.21  tff(c_16, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.21  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_setfam_1(B_7), A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.21  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.21  tff(c_23, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.21  tff(c_31, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_14, c_23])).
% 1.79/1.21  tff(c_45, plain, (![A_17, C_18, B_19]: (r1_xboole_0(A_17, C_18) | ~r1_tarski(A_17, k4_xboole_0(B_19, C_18)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.21  tff(c_54, plain, (![A_20]: (r1_xboole_0(A_20, '#skF_3') | ~r1_tarski(A_20, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_31, c_45])).
% 1.79/1.21  tff(c_12, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.21  tff(c_62, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_54, c_12])).
% 1.79/1.21  tff(c_65, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_62])).
% 1.79/1.21  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_65])).
% 1.79/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  Inference rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Ref     : 0
% 1.79/1.21  #Sup     : 12
% 1.79/1.21  #Fact    : 0
% 1.79/1.21  #Define  : 0
% 1.79/1.21  #Split   : 0
% 1.79/1.21  #Chain   : 0
% 1.79/1.21  #Close   : 0
% 1.79/1.21  
% 1.79/1.21  Ordering : KBO
% 1.79/1.21  
% 1.79/1.21  Simplification rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Subsume      : 0
% 1.79/1.21  #Demod        : 1
% 1.79/1.21  #Tautology    : 4
% 1.79/1.21  #SimpNegUnit  : 0
% 1.79/1.21  #BackRed      : 0
% 1.79/1.21  
% 1.79/1.21  #Partial instantiations: 0
% 1.79/1.21  #Strategies tried      : 1
% 1.79/1.21  
% 1.79/1.21  Timing (in seconds)
% 1.79/1.21  ----------------------
% 1.79/1.22  Preprocessing        : 0.27
% 1.79/1.22  Parsing              : 0.15
% 1.79/1.22  CNF conversion       : 0.02
% 1.79/1.22  Main loop            : 0.09
% 1.79/1.22  Inferencing          : 0.04
% 1.79/1.22  Reduction            : 0.02
% 1.79/1.22  Demodulation         : 0.02
% 1.79/1.22  BG Simplification    : 0.01
% 1.79/1.22  Subsumption          : 0.01
% 1.79/1.22  Abstraction          : 0.00
% 1.79/1.22  MUC search           : 0.00
% 1.79/1.22  Cooper               : 0.00
% 1.79/1.22  Total                : 0.39
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
