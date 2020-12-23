%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_11,C_12,B_13] :
      ( r1_tarski(A_11,k2_xboole_0(C_12,B_13))
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_16] :
      ( r1_tarski(A_16,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_16,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_47,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(k1_tarski(A_6),k1_tarski(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_47,c_10])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.11  %$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.11  
% 1.59/1.11  %Foreground sorts:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Background operators:
% 1.59/1.11  
% 1.59/1.11  
% 1.59/1.11  %Foreground operators:
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.11  
% 1.59/1.12  tff(f_44, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 1.59/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.59/1.12  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.59/1.12  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.59/1.12  tff(c_12, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.12  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.59/1.12  tff(c_28, plain, (![A_11, C_12, B_13]: (r1_tarski(A_11, k2_xboole_0(C_12, B_13)) | ~r1_tarski(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.12  tff(c_42, plain, (![A_16]: (r1_tarski(A_16, k1_tarski('#skF_1')) | ~r1_tarski(A_16, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_14, c_28])).
% 1.59/1.12  tff(c_47, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_42])).
% 1.59/1.12  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(k1_tarski(A_6), k1_tarski(B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.59/1.12  tff(c_52, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_47, c_10])).
% 1.59/1.12  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_52])).
% 1.59/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  Inference rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Ref     : 0
% 1.59/1.12  #Sup     : 9
% 1.59/1.12  #Fact    : 0
% 1.59/1.12  #Define  : 0
% 1.59/1.12  #Split   : 0
% 1.59/1.12  #Chain   : 0
% 1.59/1.12  #Close   : 0
% 1.59/1.12  
% 1.59/1.12  Ordering : KBO
% 1.59/1.12  
% 1.59/1.12  Simplification rules
% 1.59/1.12  ----------------------
% 1.59/1.12  #Subsume      : 0
% 1.59/1.12  #Demod        : 2
% 1.59/1.12  #Tautology    : 5
% 1.59/1.12  #SimpNegUnit  : 1
% 1.59/1.12  #BackRed      : 0
% 1.59/1.12  
% 1.59/1.12  #Partial instantiations: 0
% 1.59/1.12  #Strategies tried      : 1
% 1.59/1.12  
% 1.59/1.12  Timing (in seconds)
% 1.59/1.12  ----------------------
% 1.59/1.12  Preprocessing        : 0.27
% 1.59/1.12  Parsing              : 0.14
% 1.59/1.12  CNF conversion       : 0.02
% 1.59/1.12  Main loop            : 0.08
% 1.59/1.12  Inferencing          : 0.03
% 1.59/1.12  Reduction            : 0.02
% 1.59/1.12  Demodulation         : 0.02
% 1.59/1.13  BG Simplification    : 0.01
% 1.59/1.13  Subsumption          : 0.01
% 1.59/1.13  Abstraction          : 0.00
% 1.59/1.13  MUC search           : 0.00
% 1.59/1.13  Cooper               : 0.00
% 1.59/1.13  Total                : 0.37
% 1.59/1.13  Index Insertion      : 0.00
% 1.59/1.13  Index Deletion       : 0.00
% 1.59/1.13  Index Matching       : 0.00
% 1.59/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
