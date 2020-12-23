%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_37])).

tff(c_49,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_46])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [B_13,A_14] :
      ( B_13 = A_14
      | ~ r1_tarski(k1_tarski(A_14),k1_tarski(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [B_17,A_18] :
      ( B_17 = A_18
      | k4_xboole_0(k1_tarski(A_18),k1_tarski(B_17)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

tff(c_57,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_54])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.12  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.12  
% 1.60/1.12  %Foreground sorts:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Background operators:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Foreground operators:
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.60/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.12  
% 1.60/1.13  tff(f_42, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.60/1.13  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.60/1.13  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.60/1.13  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.60/1.13  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.60/1.13  tff(c_12, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.13  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.13  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.13  tff(c_37, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.13  tff(c_46, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_37])).
% 1.60/1.13  tff(c_49, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_46])).
% 1.60/1.13  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.13  tff(c_32, plain, (![B_13, A_14]: (B_13=A_14 | ~r1_tarski(k1_tarski(A_14), k1_tarski(B_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.13  tff(c_54, plain, (![B_17, A_18]: (B_17=A_18 | k4_xboole_0(k1_tarski(A_18), k1_tarski(B_17))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32])).
% 1.60/1.13  tff(c_57, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_49, c_54])).
% 1.60/1.13  tff(c_61, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_57])).
% 1.60/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  Inference rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Ref     : 0
% 1.60/1.13  #Sup     : 12
% 1.60/1.13  #Fact    : 0
% 1.60/1.13  #Define  : 0
% 1.60/1.13  #Split   : 0
% 1.60/1.13  #Chain   : 0
% 1.60/1.13  #Close   : 0
% 1.60/1.13  
% 1.60/1.13  Ordering : KBO
% 1.60/1.13  
% 1.60/1.13  Simplification rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Subsume      : 0
% 1.60/1.13  #Demod        : 1
% 1.60/1.13  #Tautology    : 9
% 1.60/1.13  #SimpNegUnit  : 1
% 1.60/1.13  #BackRed      : 0
% 1.60/1.13  
% 1.60/1.13  #Partial instantiations: 0
% 1.60/1.13  #Strategies tried      : 1
% 1.60/1.13  
% 1.60/1.13  Timing (in seconds)
% 1.60/1.13  ----------------------
% 1.60/1.13  Preprocessing        : 0.27
% 1.60/1.13  Parsing              : 0.15
% 1.60/1.13  CNF conversion       : 0.01
% 1.60/1.13  Main loop            : 0.08
% 1.60/1.13  Inferencing          : 0.03
% 1.60/1.13  Reduction            : 0.02
% 1.60/1.13  Demodulation         : 0.02
% 1.60/1.13  BG Simplification    : 0.01
% 1.60/1.13  Subsumption          : 0.01
% 1.60/1.13  Abstraction          : 0.00
% 1.60/1.13  MUC search           : 0.00
% 1.60/1.13  Cooper               : 0.00
% 1.60/1.13  Total                : 0.37
% 1.60/1.13  Index Insertion      : 0.00
% 1.60/1.13  Index Deletion       : 0.00
% 1.60/1.13  Index Matching       : 0.00
% 1.60/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
