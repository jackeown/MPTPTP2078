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
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 29.91s
% Output     : CNFRefutation 29.99s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  83 expanded)
%              Number of equality atoms :   39 (  71 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_424,plain,(
    ! [A_46,B_47] : k2_xboole_0(k3_xboole_0(A_46,B_47),k4_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_760,plain,(
    ! [A_57,B_58] : k4_xboole_0(k3_xboole_0(A_57,B_58),A_57) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_16])).

tff(c_798,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_760])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_954,plain,(
    ! [B_62,A_63] : k4_xboole_0(k3_xboole_0(B_62,A_63),A_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_760])).

tff(c_174,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_192,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_174])).

tff(c_198,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_192])).

tff(c_472,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)),k1_xboole_0) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_424])).

tff(c_488,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_472])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_689,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k4_xboole_0(A_54,B_55),k3_xboole_0(A_54,C_56)) = k4_xboole_0(A_54,k4_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_728,plain,(
    ! [B_55] : k4_xboole_0('#skF_1',k4_xboole_0(B_55,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_55),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_689])).

tff(c_754,plain,(
    ! [B_55] : k4_xboole_0('#skF_1',k4_xboole_0(B_55,'#skF_2')) = k4_xboole_0('#skF_1',B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_728])).

tff(c_960,plain,(
    ! [B_62] : k4_xboole_0('#skF_1',k3_xboole_0(B_62,'#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_754])).

tff(c_1014,plain,(
    ! [B_62] : k4_xboole_0('#skF_1',k3_xboole_0(B_62,'#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_960])).

tff(c_469,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_424])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_475,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_424])).

tff(c_489,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_475])).

tff(c_740,plain,(
    ! [A_12,B_13,C_56] : k4_xboole_0(A_12,k4_xboole_0(k2_xboole_0(A_12,B_13),C_56)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_12,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_689])).

tff(c_10512,plain,(
    ! [A_167,B_168,C_169] : k4_xboole_0(A_167,k4_xboole_0(k2_xboole_0(A_167,B_168),C_169)) = k3_xboole_0(A_167,C_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_740])).

tff(c_137074,plain,(
    ! [A_633,B_634,C_635] : k4_xboole_0(k3_xboole_0(A_633,B_634),k4_xboole_0(B_634,C_635)) = k3_xboole_0(k3_xboole_0(A_633,B_634),C_635) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_10512])).

tff(c_138068,plain,(
    ! [A_633,B_62] : k3_xboole_0(k3_xboole_0(A_633,'#skF_1'),k3_xboole_0(B_62,'#skF_2')) = k4_xboole_0(k3_xboole_0(A_633,'#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_137074])).

tff(c_138451,plain,(
    ! [A_636,B_637] : k3_xboole_0(k3_xboole_0(A_636,'#skF_1'),k3_xboole_0(B_637,'#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_138068])).

tff(c_138958,plain,(
    ! [B_2,B_637] : k3_xboole_0(k3_xboole_0('#skF_1',B_2),k3_xboole_0(B_637,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_138451])).

tff(c_145,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_153,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_29])).

tff(c_151535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138958,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.91/22.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.99/22.49  
% 29.99/22.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.99/22.49  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 29.99/22.49  
% 29.99/22.49  %Foreground sorts:
% 29.99/22.49  
% 29.99/22.49  
% 29.99/22.49  %Background operators:
% 29.99/22.49  
% 29.99/22.49  
% 29.99/22.49  %Foreground operators:
% 29.99/22.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.99/22.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 29.99/22.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.99/22.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 29.99/22.49  tff('#skF_2', type, '#skF_2': $i).
% 29.99/22.49  tff('#skF_3', type, '#skF_3': $i).
% 29.99/22.49  tff('#skF_1', type, '#skF_1': $i).
% 29.99/22.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.99/22.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.99/22.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.99/22.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.99/22.49  
% 29.99/22.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.99/22.50  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 29.99/22.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 29.99/22.50  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 29.99/22.50  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 29.99/22.50  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 29.99/22.50  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 29.99/22.50  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 29.99/22.50  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 29.99/22.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.99/22.50  tff(c_424, plain, (![A_46, B_47]: (k2_xboole_0(k3_xboole_0(A_46, B_47), k4_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.99/22.50  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.99/22.50  tff(c_760, plain, (![A_57, B_58]: (k4_xboole_0(k3_xboole_0(A_57, B_58), A_57)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_424, c_16])).
% 29.99/22.50  tff(c_798, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_760])).
% 29.99/22.50  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.99/22.50  tff(c_954, plain, (![B_62, A_63]: (k4_xboole_0(k3_xboole_0(B_62, A_63), A_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_760])).
% 29.99/22.50  tff(c_174, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.99/22.50  tff(c_192, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_174])).
% 29.99/22.50  tff(c_198, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_192])).
% 29.99/22.50  tff(c_472, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, k2_xboole_0(A_12, B_13)), k1_xboole_0)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_16, c_424])).
% 29.99/22.50  tff(c_488, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_472])).
% 29.99/22.50  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.99/22.50  tff(c_135, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.99/22.50  tff(c_139, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_135])).
% 29.99/22.50  tff(c_689, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k4_xboole_0(A_54, B_55), k3_xboole_0(A_54, C_56))=k4_xboole_0(A_54, k4_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.99/22.50  tff(c_728, plain, (![B_55]: (k4_xboole_0('#skF_1', k4_xboole_0(B_55, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_55), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_139, c_689])).
% 29.99/22.50  tff(c_754, plain, (![B_55]: (k4_xboole_0('#skF_1', k4_xboole_0(B_55, '#skF_2'))=k4_xboole_0('#skF_1', B_55))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_728])).
% 29.99/22.50  tff(c_960, plain, (![B_62]: (k4_xboole_0('#skF_1', k3_xboole_0(B_62, '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_954, c_754])).
% 29.99/22.50  tff(c_1014, plain, (![B_62]: (k4_xboole_0('#skF_1', k3_xboole_0(B_62, '#skF_2'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_960])).
% 29.99/22.50  tff(c_469, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_424])).
% 29.99/22.50  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.99/22.50  tff(c_475, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_424])).
% 29.99/22.50  tff(c_489, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_475])).
% 29.99/22.50  tff(c_740, plain, (![A_12, B_13, C_56]: (k4_xboole_0(A_12, k4_xboole_0(k2_xboole_0(A_12, B_13), C_56))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_12, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_689])).
% 29.99/22.50  tff(c_10512, plain, (![A_167, B_168, C_169]: (k4_xboole_0(A_167, k4_xboole_0(k2_xboole_0(A_167, B_168), C_169))=k3_xboole_0(A_167, C_169))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_740])).
% 29.99/22.50  tff(c_137074, plain, (![A_633, B_634, C_635]: (k4_xboole_0(k3_xboole_0(A_633, B_634), k4_xboole_0(B_634, C_635))=k3_xboole_0(k3_xboole_0(A_633, B_634), C_635))), inference(superposition, [status(thm), theory('equality')], [c_469, c_10512])).
% 29.99/22.50  tff(c_138068, plain, (![A_633, B_62]: (k3_xboole_0(k3_xboole_0(A_633, '#skF_1'), k3_xboole_0(B_62, '#skF_2'))=k4_xboole_0(k3_xboole_0(A_633, '#skF_1'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_137074])).
% 29.99/22.50  tff(c_138451, plain, (![A_636, B_637]: (k3_xboole_0(k3_xboole_0(A_636, '#skF_1'), k3_xboole_0(B_637, '#skF_2'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_798, c_138068])).
% 29.99/22.50  tff(c_138958, plain, (![B_2, B_637]: (k3_xboole_0(k3_xboole_0('#skF_1', B_2), k3_xboole_0(B_637, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_138451])).
% 29.99/22.50  tff(c_145, plain, (![A_32, B_33]: (r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.99/22.50  tff(c_26, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 29.99/22.50  tff(c_29, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 29.99/22.50  tff(c_153, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_29])).
% 29.99/22.50  tff(c_151535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138958, c_153])).
% 29.99/22.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.99/22.50  
% 29.99/22.50  Inference rules
% 29.99/22.50  ----------------------
% 29.99/22.50  #Ref     : 0
% 29.99/22.50  #Sup     : 36964
% 29.99/22.50  #Fact    : 0
% 29.99/22.50  #Define  : 0
% 29.99/22.50  #Split   : 0
% 29.99/22.50  #Chain   : 0
% 29.99/22.50  #Close   : 0
% 29.99/22.50  
% 29.99/22.50  Ordering : KBO
% 29.99/22.50  
% 29.99/22.50  Simplification rules
% 29.99/22.50  ----------------------
% 29.99/22.50  #Subsume      : 61
% 29.99/22.50  #Demod        : 46291
% 29.99/22.50  #Tautology    : 26733
% 29.99/22.50  #SimpNegUnit  : 0
% 29.99/22.50  #BackRed      : 4
% 29.99/22.50  
% 29.99/22.50  #Partial instantiations: 0
% 29.99/22.50  #Strategies tried      : 1
% 29.99/22.50  
% 29.99/22.50  Timing (in seconds)
% 29.99/22.50  ----------------------
% 29.99/22.51  Preprocessing        : 0.27
% 29.99/22.51  Parsing              : 0.16
% 29.99/22.51  CNF conversion       : 0.01
% 29.99/22.51  Main loop            : 21.50
% 29.99/22.51  Inferencing          : 2.06
% 29.99/22.51  Reduction            : 14.66
% 29.99/22.51  Demodulation         : 13.78
% 29.99/22.51  BG Simplification    : 0.26
% 29.99/22.51  Subsumption          : 3.86
% 29.99/22.51  Abstraction          : 0.52
% 29.99/22.51  MUC search           : 0.00
% 29.99/22.51  Cooper               : 0.00
% 29.99/22.51  Total                : 21.80
% 29.99/22.51  Index Insertion      : 0.00
% 29.99/22.51  Index Deletion       : 0.00
% 29.99/22.51  Index Matching       : 0.00
% 29.99/22.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
