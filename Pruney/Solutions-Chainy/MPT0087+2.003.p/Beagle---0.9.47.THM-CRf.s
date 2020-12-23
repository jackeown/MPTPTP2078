%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_337,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [A_38,B_39] : k2_xboole_0(k3_xboole_0(A_38,B_39),k4_xboole_0(A_38,B_39)) = k2_xboole_0(k3_xboole_0(A_38,B_39),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_12])).

tff(c_369,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_346])).

tff(c_52,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_23] : k2_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_398,plain,(
    ! [B_42] : k3_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_68])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_406,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_16])).

tff(c_428,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_406])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_144,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_144])).

tff(c_435,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k3_xboole_0(A_43,B_44),C_45) = k3_xboole_0(A_43,k4_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_487,plain,(
    ! [C_45] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_45)) = k4_xboole_0(k1_xboole_0,C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_435])).

tff(c_779,plain,(
    ! [C_45] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_45)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_487])).

tff(c_138,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_24])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.33  
% 2.53/1.33  %Foreground sorts:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Background operators:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Foreground operators:
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.33  
% 2.53/1.34  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.53/1.34  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.53/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.53/1.34  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.53/1.34  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.53/1.34  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.53/1.34  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.53/1.34  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.53/1.34  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.53/1.34  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.34  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.34  tff(c_337, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.34  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.34  tff(c_346, plain, (![A_38, B_39]: (k2_xboole_0(k3_xboole_0(A_38, B_39), k4_xboole_0(A_38, B_39))=k2_xboole_0(k3_xboole_0(A_38, B_39), A_38))), inference(superposition, [status(thm), theory('equality')], [c_337, c_12])).
% 2.53/1.34  tff(c_369, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k3_xboole_0(A_40, B_41))=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_346])).
% 2.53/1.34  tff(c_52, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.34  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.34  tff(c_68, plain, (![A_23]: (k2_xboole_0(k1_xboole_0, A_23)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_52, c_8])).
% 2.53/1.34  tff(c_398, plain, (![B_42]: (k3_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_369, c_68])).
% 2.53/1.34  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.34  tff(c_406, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_42))), inference(superposition, [status(thm), theory('equality')], [c_398, c_16])).
% 2.53/1.34  tff(c_428, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_406])).
% 2.53/1.34  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.34  tff(c_144, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.34  tff(c_152, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_144])).
% 2.53/1.34  tff(c_435, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k3_xboole_0(A_43, B_44), C_45)=k3_xboole_0(A_43, k4_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.34  tff(c_487, plain, (![C_45]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_45))=k4_xboole_0(k1_xboole_0, C_45))), inference(superposition, [status(thm), theory('equality')], [c_152, c_435])).
% 2.53/1.34  tff(c_779, plain, (![C_45]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_45))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_428, c_487])).
% 2.53/1.34  tff(c_138, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.34  tff(c_24, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.34  tff(c_142, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_24])).
% 2.53/1.34  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_779, c_142])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 183
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 0
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 0
% 2.53/1.34  #Demod        : 151
% 2.53/1.34  #Tautology    : 143
% 2.53/1.34  #SimpNegUnit  : 0
% 2.53/1.34  #BackRed      : 2
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.35  Preprocessing        : 0.29
% 2.53/1.35  Parsing              : 0.15
% 2.53/1.35  CNF conversion       : 0.02
% 2.53/1.35  Main loop            : 0.30
% 2.53/1.35  Inferencing          : 0.11
% 2.53/1.35  Reduction            : 0.12
% 2.53/1.35  Demodulation         : 0.09
% 2.53/1.35  BG Simplification    : 0.01
% 2.53/1.35  Subsumption          : 0.04
% 2.53/1.35  Abstraction          : 0.02
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.62
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
