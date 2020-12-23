%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [C_17,B_16] : r1_tarski(k1_tarski(C_17),k2_tarski(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_109,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [C_17,B_16] : k2_xboole_0(k1_tarski(C_17),k2_tarski(B_16,C_17)) = k2_tarski(B_16,C_17) ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_374,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(k2_tarski(A_58,B_59),k1_tarski(B_59)) = k1_tarski(A_58)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_380,plain,(
    ! [B_59,A_58] :
      ( k5_xboole_0(k1_tarski(B_59),k1_tarski(A_58)) = k2_xboole_0(k1_tarski(B_59),k2_tarski(A_58,B_59))
      | B_59 = A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_6])).

tff(c_544,plain,(
    ! [B_69,A_70] :
      ( k5_xboole_0(k1_tarski(B_69),k1_tarski(A_70)) = k2_tarski(A_70,B_69)
      | B_69 = A_70 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_380])).

tff(c_28,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_550,plain,
    ( k2_tarski('#skF_2','#skF_1') != k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_28])).

tff(c_556,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_550])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:32:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.32  
% 2.13/1.32  %Foreground sorts:
% 2.13/1.32  
% 2.13/1.32  
% 2.13/1.32  %Background operators:
% 2.13/1.32  
% 2.13/1.32  
% 2.13/1.32  %Foreground operators:
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.32  
% 2.13/1.33  tff(f_67, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.13/1.33  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.13/1.33  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.13/1.33  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.13/1.33  tff(f_61, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.13/1.33  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.13/1.33  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.33  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.33  tff(c_20, plain, (![C_17, B_16]: (r1_tarski(k1_tarski(C_17), k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.33  tff(c_109, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.33  tff(c_125, plain, (![C_17, B_16]: (k2_xboole_0(k1_tarski(C_17), k2_tarski(B_16, C_17))=k2_tarski(B_16, C_17))), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.13/1.33  tff(c_374, plain, (![A_58, B_59]: (k4_xboole_0(k2_tarski(A_58, B_59), k1_tarski(B_59))=k1_tarski(A_58) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.33  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.33  tff(c_380, plain, (![B_59, A_58]: (k5_xboole_0(k1_tarski(B_59), k1_tarski(A_58))=k2_xboole_0(k1_tarski(B_59), k2_tarski(A_58, B_59)) | B_59=A_58)), inference(superposition, [status(thm), theory('equality')], [c_374, c_6])).
% 2.13/1.33  tff(c_544, plain, (![B_69, A_70]: (k5_xboole_0(k1_tarski(B_69), k1_tarski(A_70))=k2_tarski(A_70, B_69) | B_69=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_125, c_380])).
% 2.13/1.33  tff(c_28, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.33  tff(c_550, plain, (k2_tarski('#skF_2', '#skF_1')!=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_544, c_28])).
% 2.13/1.33  tff(c_556, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_550])).
% 2.13/1.33  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_556])).
% 2.13/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.33  
% 2.13/1.33  Inference rules
% 2.13/1.33  ----------------------
% 2.13/1.33  #Ref     : 0
% 2.13/1.33  #Sup     : 127
% 2.13/1.33  #Fact    : 0
% 2.13/1.33  #Define  : 0
% 2.13/1.33  #Split   : 0
% 2.13/1.33  #Chain   : 0
% 2.13/1.33  #Close   : 0
% 2.13/1.33  
% 2.13/1.33  Ordering : KBO
% 2.13/1.33  
% 2.13/1.33  Simplification rules
% 2.13/1.33  ----------------------
% 2.13/1.33  #Subsume      : 10
% 2.13/1.33  #Demod        : 69
% 2.13/1.33  #Tautology    : 92
% 2.13/1.33  #SimpNegUnit  : 1
% 2.13/1.33  #BackRed      : 0
% 2.51/1.33  
% 2.51/1.33  #Partial instantiations: 0
% 2.51/1.33  #Strategies tried      : 1
% 2.51/1.33  
% 2.51/1.33  Timing (in seconds)
% 2.51/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.29
% 2.51/1.33  Parsing              : 0.16
% 2.51/1.33  CNF conversion       : 0.02
% 2.51/1.33  Main loop            : 0.25
% 2.51/1.33  Inferencing          : 0.09
% 2.51/1.33  Reduction            : 0.10
% 2.51/1.33  Demodulation         : 0.08
% 2.51/1.33  BG Simplification    : 0.01
% 2.51/1.33  Subsumption          : 0.04
% 2.51/1.33  Abstraction          : 0.01
% 2.51/1.33  MUC search           : 0.00
% 2.51/1.33  Cooper               : 0.00
% 2.51/1.33  Total                : 0.57
% 2.51/1.33  Index Insertion      : 0.00
% 2.51/1.33  Index Deletion       : 0.00
% 2.51/1.33  Index Matching       : 0.00
% 2.51/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
