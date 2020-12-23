%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  39 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_64,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_64])).

tff(c_190,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_190])).

tff(c_220,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_361,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k3_xboole_0(A_39,B_40),C_41) = k3_xboole_0(A_39,k4_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_413,plain,(
    ! [C_41] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_41)) = k4_xboole_0(k1_xboole_0,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_361])).

tff(c_431,plain,(
    ! [C_41] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_413])).

tff(c_56,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_20])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.25  
% 2.14/1.26  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.14/1.26  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.14/1.26  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.14/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.14/1.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.14/1.26  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.14/1.26  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.14/1.26  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.26  tff(c_18, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.26  tff(c_40, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.26  tff(c_45, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_18, c_40])).
% 2.14/1.26  tff(c_64, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.26  tff(c_82, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_64])).
% 2.14/1.26  tff(c_190, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.26  tff(c_208, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_82, c_190])).
% 2.14/1.26  tff(c_220, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_208])).
% 2.14/1.26  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.26  tff(c_85, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.14/1.26  tff(c_361, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k3_xboole_0(A_39, B_40), C_41)=k3_xboole_0(A_39, k4_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.26  tff(c_413, plain, (![C_41]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_41))=k4_xboole_0(k1_xboole_0, C_41))), inference(superposition, [status(thm), theory('equality')], [c_85, c_361])).
% 2.14/1.26  tff(c_431, plain, (![C_41]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_413])).
% 2.14/1.26  tff(c_56, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.26  tff(c_20, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.26  tff(c_63, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_20])).
% 2.14/1.26  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_63])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 113
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.26  #Split   : 0
% 2.14/1.26  #Chain   : 0
% 2.14/1.26  #Close   : 0
% 2.14/1.26  
% 2.14/1.26  Ordering : KBO
% 2.14/1.26  
% 2.14/1.26  Simplification rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Subsume      : 1
% 2.14/1.26  #Demod        : 71
% 2.14/1.26  #Tautology    : 80
% 2.14/1.26  #SimpNegUnit  : 0
% 2.14/1.26  #BackRed      : 1
% 2.14/1.26  
% 2.14/1.26  #Partial instantiations: 0
% 2.14/1.26  #Strategies tried      : 1
% 2.14/1.26  
% 2.14/1.26  Timing (in seconds)
% 2.14/1.26  ----------------------
% 2.14/1.26  Preprocessing        : 0.28
% 2.14/1.26  Parsing              : 0.15
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.23
% 2.14/1.26  Inferencing          : 0.09
% 2.14/1.26  Reduction            : 0.08
% 2.14/1.26  Demodulation         : 0.07
% 2.14/1.26  BG Simplification    : 0.01
% 2.14/1.26  Subsumption          : 0.03
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.54
% 2.14/1.26  Index Insertion      : 0.00
% 2.14/1.26  Index Deletion       : 0.00
% 2.14/1.26  Index Matching       : 0.00
% 2.14/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
