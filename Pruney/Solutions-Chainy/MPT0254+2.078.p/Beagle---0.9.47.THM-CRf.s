%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:29 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   41 (  91 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 ( 101 expanded)
%              Number of equality atoms :   23 (  88 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_22,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [A_21,B_22] :
      ( k1_xboole_0 = A_21
      | k2_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_91])).

tff(c_102,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    ! [A_6] : r1_xboole_0(A_6,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_8])).

tff(c_262,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | ~ r1_xboole_0(k1_tarski(A_35),B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_270,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_262])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_6])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | k4_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_296,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | k4_xboole_0(k1_tarski(A_42),B_43) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_303,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_2')
      | k1_tarski(A_42) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_296])).

tff(c_308,plain,(
    ! [A_42] : k1_tarski(A_42) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_303])).

tff(c_139,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_101])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.21  
% 1.93/1.22  tff(f_54, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.93/1.22  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.93/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.93/1.22  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.93/1.22  tff(f_44, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.93/1.22  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.22  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.93/1.22  tff(c_22, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.22  tff(c_91, plain, (![A_21, B_22]: (k1_xboole_0=A_21 | k2_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.22  tff(c_101, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_91])).
% 1.93/1.22  tff(c_102, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_101, c_22])).
% 1.93/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.22  tff(c_113, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_2])).
% 1.93/1.22  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.22  tff(c_134, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 1.93/1.22  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.22  tff(c_142, plain, (![A_6]: (r1_xboole_0(A_6, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_8])).
% 1.93/1.22  tff(c_262, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | ~r1_xboole_0(k1_tarski(A_35), B_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.22  tff(c_270, plain, (![A_35]: (~r2_hidden(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_262])).
% 1.93/1.22  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.22  tff(c_141, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_6])).
% 1.93/1.22  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | k4_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.22  tff(c_296, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | k4_xboole_0(k1_tarski(A_42), B_43)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_16])).
% 1.93/1.22  tff(c_303, plain, (![A_42]: (r2_hidden(A_42, '#skF_2') | k1_tarski(A_42)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_296])).
% 1.93/1.22  tff(c_308, plain, (![A_42]: (k1_tarski(A_42)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_270, c_303])).
% 1.93/1.22  tff(c_139, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_101])).
% 1.93/1.22  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_139])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 75
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 1
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 13
% 1.93/1.22  #Demod        : 37
% 1.93/1.22  #Tautology    : 50
% 1.93/1.22  #SimpNegUnit  : 2
% 1.93/1.22  #BackRed      : 8
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.22  Preprocessing        : 0.28
% 1.93/1.22  Parsing              : 0.15
% 1.93/1.22  CNF conversion       : 0.02
% 1.93/1.22  Main loop            : 0.18
% 1.93/1.22  Inferencing          : 0.06
% 1.93/1.22  Reduction            : 0.06
% 1.93/1.22  Demodulation         : 0.05
% 1.93/1.22  BG Simplification    : 0.01
% 1.93/1.22  Subsumption          : 0.03
% 1.93/1.22  Abstraction          : 0.01
% 1.93/1.22  MUC search           : 0.00
% 1.93/1.22  Cooper               : 0.00
% 1.93/1.22  Total                : 0.48
% 1.93/1.22  Index Insertion      : 0.00
% 1.93/1.22  Index Deletion       : 0.00
% 1.93/1.22  Index Matching       : 0.00
% 1.93/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
