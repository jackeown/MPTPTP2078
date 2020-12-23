%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   46 (  94 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   40 ( 104 expanded)
%              Number of equality atoms :   30 (  65 expanded)
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

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_29,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k3_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_18])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),k4_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [A_30,B_31] : k2_xboole_0(k3_xboole_0(A_30,k4_xboole_0(A_30,B_31)),k3_xboole_0(A_30,B_31)) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_458,plain,(
    ! [A_41] : k2_xboole_0(k3_xboole_0(A_41,k4_xboole_0(A_41,k1_xboole_0)),k1_xboole_0) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_176])).

tff(c_47,plain,(
    ! [A_20] : k3_xboole_0(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_34])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_8])).

tff(c_488,plain,(
    ! [A_42] : k3_xboole_0(A_42,k4_xboole_0(A_42,k1_xboole_0)) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_52])).

tff(c_107,plain,(
    ! [A_25,B_26] : k2_xboole_0(k3_xboole_0(A_25,k4_xboole_0(A_25,B_26)),k3_xboole_0(A_25,B_26)) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_504,plain,(
    ! [A_42] : k2_xboole_0(k3_xboole_0(A_42,k4_xboole_0(A_42,k4_xboole_0(A_42,k1_xboole_0))),A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_107])).

tff(c_633,plain,(
    ! [A_46] : k2_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_10,c_504])).

tff(c_74,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_12,k1_xboole_0)) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_74])).

tff(c_649,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_86])).

tff(c_464,plain,(
    ! [A_41] : k3_xboole_0(A_41,k4_xboole_0(A_41,k1_xboole_0)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_52])).

tff(c_690,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_464])).

tff(c_116,plain,(
    ! [A_27,B_28,C_29] : k3_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k3_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_34])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_45])).

tff(c_731,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_128])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:03:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  
% 2.09/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.32  
% 2.09/1.32  %Foreground sorts:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Background operators:
% 2.09/1.32  
% 2.09/1.32  
% 2.09/1.32  %Foreground operators:
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.32  
% 2.50/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.50/1.34  tff(f_46, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.50/1.34  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.50/1.34  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.50/1.34  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.50/1.34  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.50/1.34  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.50/1.34  tff(c_29, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k3_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.34  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.34  tff(c_33, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_18])).
% 2.50/1.34  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.34  tff(c_34, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.34  tff(c_46, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_34])).
% 2.50/1.34  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.34  tff(c_98, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.34  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k4_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.34  tff(c_176, plain, (![A_30, B_31]: (k2_xboole_0(k3_xboole_0(A_30, k4_xboole_0(A_30, B_31)), k3_xboole_0(A_30, B_31))=A_30)), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 2.50/1.34  tff(c_458, plain, (![A_41]: (k2_xboole_0(k3_xboole_0(A_41, k4_xboole_0(A_41, k1_xboole_0)), k1_xboole_0)=A_41)), inference(superposition, [status(thm), theory('equality')], [c_46, c_176])).
% 2.50/1.34  tff(c_47, plain, (![A_20]: (k3_xboole_0(A_20, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_34])).
% 2.50/1.34  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.34  tff(c_52, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(superposition, [status(thm), theory('equality')], [c_47, c_8])).
% 2.50/1.34  tff(c_488, plain, (![A_42]: (k3_xboole_0(A_42, k4_xboole_0(A_42, k1_xboole_0))=A_42)), inference(superposition, [status(thm), theory('equality')], [c_458, c_52])).
% 2.50/1.34  tff(c_107, plain, (![A_25, B_26]: (k2_xboole_0(k3_xboole_0(A_25, k4_xboole_0(A_25, B_26)), k3_xboole_0(A_25, B_26))=A_25)), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 2.50/1.34  tff(c_504, plain, (![A_42]: (k2_xboole_0(k3_xboole_0(A_42, k4_xboole_0(A_42, k4_xboole_0(A_42, k1_xboole_0))), A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_488, c_107])).
% 2.50/1.34  tff(c_633, plain, (![A_46]: (k2_xboole_0(k1_xboole_0, A_46)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_10, c_504])).
% 2.50/1.34  tff(c_74, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.34  tff(c_86, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_12, k1_xboole_0))=A_12)), inference(superposition, [status(thm), theory('equality')], [c_46, c_74])).
% 2.50/1.34  tff(c_649, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_633, c_86])).
% 2.50/1.34  tff(c_464, plain, (![A_41]: (k3_xboole_0(A_41, k4_xboole_0(A_41, k1_xboole_0))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_458, c_52])).
% 2.50/1.34  tff(c_690, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_649, c_464])).
% 2.50/1.34  tff(c_116, plain, (![A_27, B_28, C_29]: (k3_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k3_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.34  tff(c_16, plain, (r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.34  tff(c_45, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_34])).
% 2.50/1.34  tff(c_128, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_116, c_45])).
% 2.50/1.34  tff(c_731, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_690, c_128])).
% 2.50/1.34  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_731])).
% 2.50/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  Inference rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Ref     : 0
% 2.50/1.34  #Sup     : 178
% 2.50/1.34  #Fact    : 0
% 2.50/1.34  #Define  : 0
% 2.50/1.34  #Split   : 0
% 2.50/1.34  #Chain   : 0
% 2.50/1.34  #Close   : 0
% 2.50/1.34  
% 2.50/1.34  Ordering : KBO
% 2.50/1.34  
% 2.50/1.34  Simplification rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Subsume      : 0
% 2.50/1.34  #Demod        : 114
% 2.50/1.34  #Tautology    : 124
% 2.50/1.34  #SimpNegUnit  : 1
% 2.50/1.34  #BackRed      : 6
% 2.50/1.34  
% 2.50/1.34  #Partial instantiations: 0
% 2.50/1.34  #Strategies tried      : 1
% 2.50/1.34  
% 2.50/1.34  Timing (in seconds)
% 2.50/1.34  ----------------------
% 2.50/1.34  Preprocessing        : 0.26
% 2.50/1.34  Parsing              : 0.15
% 2.50/1.34  CNF conversion       : 0.01
% 2.50/1.34  Main loop            : 0.31
% 2.50/1.34  Inferencing          : 0.12
% 2.50/1.34  Reduction            : 0.11
% 2.50/1.34  Demodulation         : 0.09
% 2.50/1.34  BG Simplification    : 0.01
% 2.50/1.34  Subsumption          : 0.04
% 2.50/1.34  Abstraction          : 0.02
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.59
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
