%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   42 (  75 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  65 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_147,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_147])).

tff(c_185,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_175,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_190,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_175])).

tff(c_983,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k4_xboole_0(A_67,B_68),k4_xboole_0(A_67,C_69)) = k4_xboole_0(A_67,k3_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1059,plain,(
    ! [A_9,B_68] : k4_xboole_0(A_9,k3_xboole_0(B_68,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_9,B_68),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_983])).

tff(c_1083,plain,(
    ! [A_9,B_68] : k2_xboole_0(k4_xboole_0(A_9,B_68),A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_190,c_1059])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_772,plain,(
    ! [A_60,B_61] : k2_xboole_0(k4_xboole_0(A_60,B_61),k4_xboole_0(B_61,A_60)) = k5_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_834,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_15,B_16),A_15),k1_xboole_0) = k5_xboole_0(k2_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_772])).

tff(c_3023,plain,(
    ! [A_112,B_113] : k5_xboole_0(k2_xboole_0(A_112,B_113),A_112) = k4_xboole_0(k2_xboole_0(A_112,B_113),A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_834])).

tff(c_3054,plain,(
    ! [A_9,B_68] : k4_xboole_0(k2_xboole_0(k4_xboole_0(A_9,B_68),A_9),k4_xboole_0(A_9,B_68)) = k5_xboole_0(A_9,k4_xboole_0(A_9,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_3023])).

tff(c_3387,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k4_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1083,c_3054])).

tff(c_3471,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3387])).

tff(c_3505,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_3471])).

tff(c_28,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3505,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.80  
% 4.37/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.80  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.37/1.80  
% 4.37/1.80  %Foreground sorts:
% 4.37/1.80  
% 4.37/1.80  
% 4.37/1.80  %Background operators:
% 4.37/1.80  
% 4.37/1.80  
% 4.37/1.80  %Foreground operators:
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.80  
% 4.37/1.81  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.37/1.81  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.37/1.81  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.37/1.81  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.37/1.81  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.37/1.81  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 4.37/1.81  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.37/1.81  tff(f_56, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.37/1.81  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.81  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.81  tff(c_147, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.81  tff(c_160, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k3_xboole_0(A_19, k4_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_147])).
% 4.37/1.81  tff(c_185, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_160])).
% 4.37/1.81  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.81  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.81  tff(c_64, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.81  tff(c_74, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 4.37/1.81  tff(c_175, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 4.37/1.81  tff(c_190, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_175])).
% 4.37/1.81  tff(c_983, plain, (![A_67, B_68, C_69]: (k2_xboole_0(k4_xboole_0(A_67, B_68), k4_xboole_0(A_67, C_69))=k4_xboole_0(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.37/1.81  tff(c_1059, plain, (![A_9, B_68]: (k4_xboole_0(A_9, k3_xboole_0(B_68, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_9, B_68), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_983])).
% 4.37/1.81  tff(c_1083, plain, (![A_9, B_68]: (k2_xboole_0(k4_xboole_0(A_9, B_68), A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_190, c_1059])).
% 4.37/1.81  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.81  tff(c_772, plain, (![A_60, B_61]: (k2_xboole_0(k4_xboole_0(A_60, B_61), k4_xboole_0(B_61, A_60))=k5_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.81  tff(c_834, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_15, B_16), A_15), k1_xboole_0)=k5_xboole_0(k2_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_772])).
% 4.37/1.81  tff(c_3023, plain, (![A_112, B_113]: (k5_xboole_0(k2_xboole_0(A_112, B_113), A_112)=k4_xboole_0(k2_xboole_0(A_112, B_113), A_112))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_834])).
% 4.37/1.81  tff(c_3054, plain, (![A_9, B_68]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_9, B_68), A_9), k4_xboole_0(A_9, B_68))=k5_xboole_0(A_9, k4_xboole_0(A_9, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_1083, c_3023])).
% 4.37/1.81  tff(c_3387, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k4_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1083, c_3054])).
% 4.37/1.81  tff(c_3471, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k3_xboole_0(A_19, k4_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3387])).
% 4.37/1.81  tff(c_3505, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_3471])).
% 4.37/1.81  tff(c_28, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.37/1.81  tff(c_5997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3505, c_28])).
% 4.37/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  
% 4.37/1.81  Inference rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Ref     : 1
% 4.37/1.81  #Sup     : 1471
% 4.37/1.81  #Fact    : 0
% 4.37/1.81  #Define  : 0
% 4.37/1.81  #Split   : 0
% 4.37/1.81  #Chain   : 0
% 4.37/1.81  #Close   : 0
% 4.37/1.81  
% 4.37/1.81  Ordering : KBO
% 4.37/1.81  
% 4.37/1.81  Simplification rules
% 4.37/1.81  ----------------------
% 4.37/1.81  #Subsume      : 9
% 4.37/1.81  #Demod        : 1301
% 4.37/1.81  #Tautology    : 986
% 4.37/1.81  #SimpNegUnit  : 0
% 4.37/1.81  #BackRed      : 4
% 4.37/1.81  
% 4.37/1.81  #Partial instantiations: 0
% 4.37/1.81  #Strategies tried      : 1
% 4.37/1.81  
% 4.37/1.81  Timing (in seconds)
% 4.37/1.81  ----------------------
% 4.55/1.81  Preprocessing        : 0.27
% 4.55/1.81  Parsing              : 0.15
% 4.55/1.81  CNF conversion       : 0.02
% 4.55/1.81  Main loop            : 0.79
% 4.55/1.81  Inferencing          : 0.26
% 4.55/1.81  Reduction            : 0.35
% 4.55/1.81  Demodulation         : 0.28
% 4.55/1.81  BG Simplification    : 0.03
% 4.55/1.81  Subsumption          : 0.10
% 4.55/1.81  Abstraction          : 0.05
% 4.55/1.81  MUC search           : 0.00
% 4.55/1.81  Cooper               : 0.00
% 4.55/1.81  Total                : 1.08
% 4.55/1.81  Index Insertion      : 0.00
% 4.55/1.81  Index Deletion       : 0.00
% 4.55/1.81  Index Matching       : 0.00
% 4.55/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
