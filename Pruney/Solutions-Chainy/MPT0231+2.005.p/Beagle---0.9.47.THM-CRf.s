%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:15 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k1_tarski(A_18),k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,k2_xboole_0(C_36,B_37))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_38,B_39,A_40] :
      ( r1_tarski(A_38,k2_xboole_0(B_39,A_40))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_179,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_44,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_140])).

tff(c_184,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_179])).

tff(c_18,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | ~ r1_tarski(k1_tarski(A_20),k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_190,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_184,c_18])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.18  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.89/1.18  
% 1.89/1.18  %Foreground sorts:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Background operators:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Foreground operators:
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.18  
% 1.89/1.19  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.89/1.19  tff(f_45, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.89/1.19  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.89/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.89/1.19  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.89/1.19  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.89/1.19  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.89/1.19  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.19  tff(c_22, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.89/1.19  tff(c_76, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.19  tff(c_88, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_22, c_76])).
% 1.89/1.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.19  tff(c_123, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, k2_xboole_0(C_36, B_37)) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_140, plain, (![A_38, B_39, A_40]: (r1_tarski(A_38, k2_xboole_0(B_39, A_40)) | ~r1_tarski(A_38, B_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_123])).
% 1.89/1.19  tff(c_179, plain, (![A_44]: (r1_tarski(A_44, k1_tarski('#skF_3')) | ~r1_tarski(A_44, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_140])).
% 1.89/1.19  tff(c_184, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_179])).
% 1.89/1.19  tff(c_18, plain, (![B_21, A_20]: (B_21=A_20 | ~r1_tarski(k1_tarski(A_20), k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.19  tff(c_190, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_184, c_18])).
% 1.89/1.19  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_190])).
% 1.89/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  Inference rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Ref     : 0
% 1.89/1.19  #Sup     : 44
% 1.89/1.19  #Fact    : 0
% 1.89/1.19  #Define  : 0
% 1.89/1.19  #Split   : 0
% 1.89/1.19  #Chain   : 0
% 1.89/1.19  #Close   : 0
% 1.89/1.19  
% 1.89/1.19  Ordering : KBO
% 1.89/1.19  
% 1.89/1.19  Simplification rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Subsume      : 3
% 1.89/1.19  #Demod        : 3
% 1.89/1.19  #Tautology    : 28
% 1.89/1.19  #SimpNegUnit  : 1
% 1.89/1.19  #BackRed      : 0
% 1.89/1.19  
% 1.89/1.19  #Partial instantiations: 0
% 1.89/1.19  #Strategies tried      : 1
% 1.89/1.19  
% 1.89/1.19  Timing (in seconds)
% 1.89/1.19  ----------------------
% 1.96/1.19  Preprocessing        : 0.28
% 1.96/1.19  Parsing              : 0.15
% 1.96/1.19  CNF conversion       : 0.02
% 1.96/1.19  Main loop            : 0.15
% 1.96/1.19  Inferencing          : 0.06
% 1.96/1.19  Reduction            : 0.05
% 1.96/1.19  Demodulation         : 0.04
% 1.96/1.19  BG Simplification    : 0.01
% 1.96/1.19  Subsumption          : 0.02
% 1.96/1.19  Abstraction          : 0.01
% 1.96/1.19  MUC search           : 0.00
% 1.96/1.19  Cooper               : 0.00
% 1.96/1.19  Total                : 0.45
% 1.96/1.19  Index Insertion      : 0.00
% 1.96/1.19  Index Deletion       : 0.00
% 1.96/1.19  Index Matching       : 0.00
% 1.96/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
