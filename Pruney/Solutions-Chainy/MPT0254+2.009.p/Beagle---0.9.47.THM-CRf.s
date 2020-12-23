%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:21 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_70,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_70])).

tff(c_207,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_225,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_73,c_207])).

tff(c_231,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_12])).

tff(c_42,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_83,plain,(
    ! [D_40,A_41] : r2_hidden(D_40,k2_tarski(A_41,D_40)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_255,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_86])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden(A_31,B_32)
      | ~ r1_xboole_0(k1_tarski(A_31),B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_320,plain,(
    ! [B_66] :
      ( ~ r2_hidden('#skF_3',B_66)
      | ~ r1_xboole_0(k1_xboole_0,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_50])).

tff(c_336,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_255,c_320])).

tff(c_343,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_336])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.32/1.33  
% 2.32/1.33  %Foreground sorts:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Background operators:
% 2.32/1.33  
% 2.32/1.33  
% 2.32/1.33  %Foreground operators:
% 2.32/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.32/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.33  
% 2.32/1.34  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.32/1.34  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.32/1.34  tff(f_75, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.32/1.34  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.32/1.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.32/1.34  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.32/1.34  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.32/1.34  tff(f_69, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.32/1.34  tff(c_12, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.34  tff(c_20, plain, (![A_11, B_12]: (r1_xboole_0(A_11, B_12) | k4_xboole_0(A_11, B_12)!=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.32/1.34  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.32/1.34  tff(c_70, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.34  tff(c_73, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_70])).
% 2.32/1.34  tff(c_207, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.34  tff(c_225, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_73, c_207])).
% 2.32/1.34  tff(c_231, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_225, c_12])).
% 2.32/1.34  tff(c_42, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.32/1.34  tff(c_83, plain, (![D_40, A_41]: (r2_hidden(D_40, k2_tarski(A_41, D_40)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.34  tff(c_86, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_83])).
% 2.32/1.34  tff(c_255, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_86])).
% 2.32/1.34  tff(c_50, plain, (![A_31, B_32]: (~r2_hidden(A_31, B_32) | ~r1_xboole_0(k1_tarski(A_31), B_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.32/1.34  tff(c_320, plain, (![B_66]: (~r2_hidden('#skF_3', B_66) | ~r1_xboole_0(k1_xboole_0, B_66))), inference(superposition, [status(thm), theory('equality')], [c_231, c_50])).
% 2.32/1.34  tff(c_336, plain, (~r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_255, c_320])).
% 2.32/1.34  tff(c_343, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_336])).
% 2.32/1.34  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_343])).
% 2.32/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  Inference rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Ref     : 0
% 2.32/1.34  #Sup     : 74
% 2.32/1.34  #Fact    : 0
% 2.32/1.34  #Define  : 0
% 2.32/1.34  #Split   : 0
% 2.32/1.34  #Chain   : 0
% 2.32/1.34  #Close   : 0
% 2.32/1.34  
% 2.32/1.34  Ordering : KBO
% 2.32/1.34  
% 2.32/1.34  Simplification rules
% 2.32/1.34  ----------------------
% 2.32/1.34  #Subsume      : 0
% 2.32/1.34  #Demod        : 18
% 2.32/1.34  #Tautology    : 51
% 2.32/1.34  #SimpNegUnit  : 0
% 2.32/1.34  #BackRed      : 3
% 2.32/1.34  
% 2.32/1.34  #Partial instantiations: 0
% 2.32/1.34  #Strategies tried      : 1
% 2.32/1.34  
% 2.32/1.34  Timing (in seconds)
% 2.32/1.34  ----------------------
% 2.32/1.34  Preprocessing        : 0.38
% 2.32/1.34  Parsing              : 0.22
% 2.32/1.34  CNF conversion       : 0.02
% 2.32/1.34  Main loop            : 0.18
% 2.32/1.34  Inferencing          : 0.06
% 2.32/1.35  Reduction            : 0.06
% 2.32/1.35  Demodulation         : 0.05
% 2.32/1.35  BG Simplification    : 0.01
% 2.32/1.35  Subsumption          : 0.03
% 2.32/1.35  Abstraction          : 0.01
% 2.32/1.35  MUC search           : 0.00
% 2.32/1.35  Cooper               : 0.00
% 2.32/1.35  Total                : 0.59
% 2.32/1.35  Index Insertion      : 0.00
% 2.32/1.35  Index Deletion       : 0.00
% 2.32/1.35  Index Matching       : 0.00
% 2.32/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
