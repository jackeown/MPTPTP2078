%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   44 (  73 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   38 (  69 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_60,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_18])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_247,plain,(
    ! [A_33,B_34] : k2_xboole_0(k3_xboole_0(A_33,k4_xboole_0(A_33,B_34)),k3_xboole_0(A_33,B_34)) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_14])).

tff(c_457,plain,(
    ! [A_40] : k2_xboole_0(k3_xboole_0(A_40,k4_xboole_0(A_40,k1_xboole_0)),k1_xboole_0) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_247])).

tff(c_26,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_26])).

tff(c_487,plain,(
    ! [A_41] : k3_xboole_0(A_41,k4_xboole_0(A_41,k1_xboole_0)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_35])).

tff(c_102,plain,(
    ! [A_24,B_25] : k2_xboole_0(k3_xboole_0(A_24,k4_xboole_0(A_24,B_25)),k3_xboole_0(A_24,B_25)) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_14])).

tff(c_503,plain,(
    ! [A_41] : k2_xboole_0(k3_xboole_0(A_41,k4_xboole_0(A_41,k4_xboole_0(A_41,k1_xboole_0))),A_41) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_102])).

tff(c_632,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_12,c_503])).

tff(c_69,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_8,k1_xboole_0)) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_651,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_81])).

tff(c_463,plain,(
    ! [A_40] : k3_xboole_0(A_40,k4_xboole_0(A_40,k1_xboole_0)) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_35])).

tff(c_695,plain,(
    ! [A_40] : k3_xboole_0(A_40,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_463])).

tff(c_111,plain,(
    ! [A_26,B_27,C_28] : k3_xboole_0(k3_xboole_0(A_26,B_27),C_28) = k3_xboole_0(A_26,k3_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_51])).

tff(c_737,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_123])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  
% 2.32/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.38  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.32/1.38  
% 2.32/1.38  %Foreground sorts:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Background operators:
% 2.32/1.38  
% 2.32/1.38  
% 2.32/1.38  %Foreground operators:
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.32/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.38  
% 2.56/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.56/1.39  tff(f_46, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.56/1.39  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.56/1.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.56/1.39  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.56/1.39  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.56/1.39  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.56/1.39  tff(c_60, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.39  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.39  tff(c_68, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_18])).
% 2.56/1.39  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.39  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.39  tff(c_93, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.39  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.39  tff(c_247, plain, (![A_33, B_34]: (k2_xboole_0(k3_xboole_0(A_33, k4_xboole_0(A_33, B_34)), k3_xboole_0(A_33, B_34))=A_33)), inference(superposition, [status(thm), theory('equality')], [c_93, c_14])).
% 2.56/1.39  tff(c_457, plain, (![A_40]: (k2_xboole_0(k3_xboole_0(A_40, k4_xboole_0(A_40, k1_xboole_0)), k1_xboole_0)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_10, c_247])).
% 2.56/1.39  tff(c_26, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k3_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.39  tff(c_35, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_10, c_26])).
% 2.56/1.39  tff(c_487, plain, (![A_41]: (k3_xboole_0(A_41, k4_xboole_0(A_41, k1_xboole_0))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_457, c_35])).
% 2.56/1.39  tff(c_102, plain, (![A_24, B_25]: (k2_xboole_0(k3_xboole_0(A_24, k4_xboole_0(A_24, B_25)), k3_xboole_0(A_24, B_25))=A_24)), inference(superposition, [status(thm), theory('equality')], [c_93, c_14])).
% 2.56/1.39  tff(c_503, plain, (![A_41]: (k2_xboole_0(k3_xboole_0(A_41, k4_xboole_0(A_41, k4_xboole_0(A_41, k1_xboole_0))), A_41)=A_41)), inference(superposition, [status(thm), theory('equality')], [c_487, c_102])).
% 2.56/1.39  tff(c_632, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_12, c_503])).
% 2.56/1.39  tff(c_69, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.39  tff(c_81, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_8, k1_xboole_0))=A_8)), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 2.56/1.39  tff(c_651, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_632, c_81])).
% 2.56/1.39  tff(c_463, plain, (![A_40]: (k3_xboole_0(A_40, k4_xboole_0(A_40, k1_xboole_0))=A_40)), inference(superposition, [status(thm), theory('equality')], [c_457, c_35])).
% 2.56/1.39  tff(c_695, plain, (![A_40]: (k3_xboole_0(A_40, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_651, c_463])).
% 2.56/1.39  tff(c_111, plain, (![A_26, B_27, C_28]: (k3_xboole_0(k3_xboole_0(A_26, B_27), C_28)=k3_xboole_0(A_26, k3_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.39  tff(c_16, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.39  tff(c_47, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.39  tff(c_51, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_47])).
% 2.56/1.39  tff(c_123, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_51])).
% 2.56/1.39  tff(c_737, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_695, c_123])).
% 2.56/1.39  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_737])).
% 2.56/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  Inference rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Ref     : 0
% 2.56/1.39  #Sup     : 181
% 2.56/1.39  #Fact    : 0
% 2.56/1.39  #Define  : 0
% 2.56/1.39  #Split   : 0
% 2.56/1.39  #Chain   : 0
% 2.56/1.39  #Close   : 0
% 2.56/1.39  
% 2.56/1.39  Ordering : KBO
% 2.56/1.39  
% 2.56/1.39  Simplification rules
% 2.56/1.39  ----------------------
% 2.56/1.39  #Subsume      : 0
% 2.56/1.39  #Demod        : 118
% 2.56/1.39  #Tautology    : 126
% 2.56/1.39  #SimpNegUnit  : 1
% 2.56/1.39  #BackRed      : 7
% 2.56/1.39  
% 2.56/1.39  #Partial instantiations: 0
% 2.56/1.39  #Strategies tried      : 1
% 2.56/1.39  
% 2.56/1.39  Timing (in seconds)
% 2.56/1.39  ----------------------
% 2.56/1.40  Preprocessing        : 0.27
% 2.56/1.40  Parsing              : 0.16
% 2.56/1.40  CNF conversion       : 0.02
% 2.56/1.40  Main loop            : 0.30
% 2.56/1.40  Inferencing          : 0.12
% 2.56/1.40  Reduction            : 0.11
% 2.56/1.40  Demodulation         : 0.09
% 2.56/1.40  BG Simplification    : 0.01
% 2.56/1.40  Subsumption          : 0.04
% 2.56/1.40  Abstraction          : 0.01
% 2.56/1.40  MUC search           : 0.00
% 2.56/1.40  Cooper               : 0.00
% 2.56/1.40  Total                : 0.60
% 2.56/1.40  Index Insertion      : 0.00
% 2.56/1.40  Index Deletion       : 0.00
% 2.56/1.40  Index Matching       : 0.00
% 2.56/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
