%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  79 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_99,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_12])).

tff(c_116,plain,(
    ! [A_24] : k3_xboole_0(A_24,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_120,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_xboole_0(A_25,C_26)
      | ~ r1_xboole_0(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    ! [A_29] :
      ( r1_xboole_0(A_29,'#skF_3')
      | ~ r1_tarski(A_29,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [A_31] :
      ( r1_xboole_0('#skF_3',A_31)
      | ~ r1_tarski(A_31,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_152,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [A_39] :
      ( k3_xboole_0('#skF_3',A_39) = k1_xboole_0
      | ~ r1_tarski(A_39,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_296,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_292])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_421,plain,(
    ! [A_46,B_47,A_48] :
      ( r1_xboole_0(A_46,B_47)
      | ~ r1_tarski(A_46,A_48)
      | k3_xboole_0(A_48,B_47) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_428,plain,(
    ! [B_49] :
      ( r1_xboole_0('#skF_1',B_49)
      | k3_xboole_0('#skF_3',B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_421])).

tff(c_473,plain,(
    ! [B_53] :
      ( k3_xboole_0('#skF_1',B_53) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_428,c_2])).

tff(c_479,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_473])).

tff(c_495,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_479])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.40  
% 2.42/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.40  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.40  
% 2.42/1.40  %Foreground sorts:
% 2.42/1.40  
% 2.42/1.40  
% 2.42/1.40  %Background operators:
% 2.42/1.40  
% 2.42/1.40  
% 2.42/1.40  %Foreground operators:
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.40  
% 2.42/1.42  tff(f_54, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.42/1.42  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.42/1.42  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.42/1.42  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.42/1.42  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.42/1.42  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.42/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.42/1.42  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.42  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.42  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.42  tff(c_80, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.42  tff(c_95, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.42/1.42  tff(c_99, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95])).
% 2.42/1.42  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.42/1.42  tff(c_104, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_99, c_12])).
% 2.42/1.42  tff(c_116, plain, (![A_24]: (k3_xboole_0(A_24, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_104])).
% 2.42/1.42  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.42  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.42  tff(c_120, plain, (![A_25, C_26, B_27]: (r1_xboole_0(A_25, C_26) | ~r1_xboole_0(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.42  tff(c_152, plain, (![A_29]: (r1_xboole_0(A_29, '#skF_3') | ~r1_tarski(A_29, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_120])).
% 2.42/1.42  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.42  tff(c_174, plain, (![A_31]: (r1_xboole_0('#skF_3', A_31) | ~r1_tarski(A_31, '#skF_2'))), inference(resolution, [status(thm)], [c_152, c_6])).
% 2.42/1.42  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.42  tff(c_292, plain, (![A_39]: (k3_xboole_0('#skF_3', A_39)=k1_xboole_0 | ~r1_tarski(A_39, '#skF_2'))), inference(resolution, [status(thm)], [c_174, c_2])).
% 2.42/1.42  tff(c_296, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_292])).
% 2.42/1.42  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.42  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.42  tff(c_421, plain, (![A_46, B_47, A_48]: (r1_xboole_0(A_46, B_47) | ~r1_tarski(A_46, A_48) | k3_xboole_0(A_48, B_47)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_120])).
% 2.42/1.42  tff(c_428, plain, (![B_49]: (r1_xboole_0('#skF_1', B_49) | k3_xboole_0('#skF_3', B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_421])).
% 2.42/1.42  tff(c_473, plain, (![B_53]: (k3_xboole_0('#skF_1', B_53)=k1_xboole_0 | k3_xboole_0('#skF_3', B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_428, c_2])).
% 2.42/1.42  tff(c_479, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_296, c_473])).
% 2.42/1.42  tff(c_495, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_479])).
% 2.42/1.42  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_495])).
% 2.42/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.42  
% 2.42/1.42  Inference rules
% 2.42/1.42  ----------------------
% 2.42/1.42  #Ref     : 0
% 2.42/1.42  #Sup     : 134
% 2.42/1.42  #Fact    : 0
% 2.42/1.42  #Define  : 0
% 2.42/1.42  #Split   : 3
% 2.42/1.42  #Chain   : 0
% 2.42/1.42  #Close   : 0
% 2.42/1.42  
% 2.42/1.42  Ordering : KBO
% 2.42/1.42  
% 2.42/1.42  Simplification rules
% 2.42/1.42  ----------------------
% 2.42/1.42  #Subsume      : 7
% 2.42/1.42  #Demod        : 51
% 2.42/1.42  #Tautology    : 66
% 2.42/1.42  #SimpNegUnit  : 1
% 2.42/1.42  #BackRed      : 0
% 2.42/1.42  
% 2.42/1.42  #Partial instantiations: 0
% 2.42/1.42  #Strategies tried      : 1
% 2.42/1.42  
% 2.42/1.42  Timing (in seconds)
% 2.42/1.42  ----------------------
% 2.42/1.42  Preprocessing        : 0.34
% 2.42/1.42  Parsing              : 0.18
% 2.42/1.42  CNF conversion       : 0.02
% 2.42/1.42  Main loop            : 0.29
% 2.42/1.42  Inferencing          : 0.11
% 2.42/1.42  Reduction            : 0.08
% 2.42/1.42  Demodulation         : 0.06
% 2.42/1.42  BG Simplification    : 0.01
% 2.42/1.42  Subsumption          : 0.06
% 2.42/1.42  Abstraction          : 0.01
% 2.42/1.42  MUC search           : 0.00
% 2.42/1.42  Cooper               : 0.00
% 2.42/1.42  Total                : 0.66
% 2.42/1.42  Index Insertion      : 0.00
% 2.42/1.42  Index Deletion       : 0.00
% 2.42/1.42  Index Matching       : 0.00
% 2.42/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
