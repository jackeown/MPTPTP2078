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
% DateTime   : Thu Dec  3 09:51:25 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  42 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_53,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_30])).

tff(c_105,plain,(
    ! [A_27,B_28] :
      ( k1_xboole_0 = A_27
      | k2_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_105])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_10])).

tff(c_189,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    ! [A_38] : ~ r2_hidden(A_38,'#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_189])).

tff(c_119,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_129,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_119])).

tff(c_14,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_136,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_14])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.80/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.16  
% 1.80/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.80/1.17  tff(f_59, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.80/1.17  tff(f_35, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.80/1.17  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.80/1.17  tff(f_55, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.80/1.17  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.80/1.17  tff(c_53, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.17  tff(c_30, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.80/1.17  tff(c_68, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_53, c_30])).
% 1.80/1.17  tff(c_105, plain, (![A_27, B_28]: (k1_xboole_0=A_27 | k2_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.17  tff(c_118, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68, c_105])).
% 1.80/1.17  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.17  tff(c_124, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_10])).
% 1.80/1.17  tff(c_189, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.17  tff(c_197, plain, (![A_38]: (~r2_hidden(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_124, c_189])).
% 1.80/1.17  tff(c_119, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30, c_105])).
% 1.80/1.17  tff(c_129, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_119])).
% 1.80/1.17  tff(c_14, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.17  tff(c_136, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_14])).
% 1.80/1.17  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_136])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 42
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 0
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 5
% 1.80/1.17  #Demod        : 17
% 1.80/1.17  #Tautology    : 30
% 1.80/1.17  #SimpNegUnit  : 1
% 1.80/1.17  #BackRed      : 6
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.18  Preprocessing        : 0.28
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.13
% 1.80/1.18  Inferencing          : 0.04
% 1.80/1.18  Reduction            : 0.05
% 1.80/1.18  Demodulation         : 0.04
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.02
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.44
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
