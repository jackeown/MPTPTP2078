%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:53 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 107 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 (  97 expanded)
%              Number of equality atoms :   40 (  96 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [A_27] : k2_xboole_0(k1_xboole_0,A_27) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_290,plain,(
    ! [A_37,B_38] : k2_xboole_0(k3_xboole_0(A_37,B_38),k4_xboole_0(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_317,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_290])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [A_31,B_32] : k4_xboole_0(k2_xboole_0(A_31,B_32),B_32) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1227,plain,(
    ! [A_65,B_66] : k4_xboole_0(k2_xboole_0(A_65,B_66),A_65) = k4_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_1245,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,k2_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_22])).

tff(c_1533,plain,(
    ! [A_72,B_73] : k2_xboole_0(A_72,k2_xboole_0(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1245])).

tff(c_1575,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = k2_xboole_0(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_1533])).

tff(c_1635,plain,(
    ! [A_74,B_75] : k2_xboole_0(A_74,k3_xboole_0(B_75,A_74)) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_2,c_1575])).

tff(c_1658,plain,(
    ! [B_75] : k3_xboole_0(B_75,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_92])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_227,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_227])).

tff(c_1770,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_254])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_583,plain,(
    ! [A_46,B_47] : k2_xboole_0(k4_xboole_0(A_46,B_47),k4_xboole_0(B_47,A_46)) = k5_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2244,plain,(
    ! [B_85,A_86] : k2_xboole_0(k4_xboole_0(B_85,A_86),k4_xboole_0(A_86,B_85)) = k5_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_583])).

tff(c_2299,plain,(
    ! [B_4,A_3] : k2_xboole_0(k4_xboole_0(k3_xboole_0(B_4,A_3),A_3),k4_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,k3_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2244])).

tff(c_3994,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k3_xboole_0(B_117,A_116)) = k4_xboole_0(A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1658,c_2,c_1770,c_2,c_18,c_2299])).

tff(c_4035,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(B_4,A_3)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3994])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.87  
% 4.21/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.87  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.21/1.87  
% 4.21/1.87  %Foreground sorts:
% 4.21/1.87  
% 4.21/1.87  
% 4.21/1.87  %Background operators:
% 4.21/1.87  
% 4.21/1.87  
% 4.21/1.87  %Foreground operators:
% 4.21/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.21/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.21/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.21/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.21/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.21/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.21/1.87  
% 4.55/1.89  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.55/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.55/1.89  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.55/1.89  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.55/1.89  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.55/1.89  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.55/1.89  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.55/1.89  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.55/1.89  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.55/1.89  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.55/1.89  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.55/1.89  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.55/1.89  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.55/1.89  tff(c_76, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.89  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.55/1.89  tff(c_92, plain, (![A_27]: (k2_xboole_0(k1_xboole_0, A_27)=A_27)), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 4.55/1.89  tff(c_290, plain, (![A_37, B_38]: (k2_xboole_0(k3_xboole_0(A_37, B_38), k4_xboole_0(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.89  tff(c_317, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_290])).
% 4.55/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.89  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.55/1.89  tff(c_178, plain, (![A_31, B_32]: (k4_xboole_0(k2_xboole_0(A_31, B_32), B_32)=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.89  tff(c_1227, plain, (![A_65, B_66]: (k4_xboole_0(k2_xboole_0(A_65, B_66), A_65)=k4_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 4.55/1.89  tff(c_1245, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, k2_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_1227, c_22])).
% 4.55/1.89  tff(c_1533, plain, (![A_72, B_73]: (k2_xboole_0(A_72, k2_xboole_0(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1245])).
% 4.55/1.89  tff(c_1575, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=k2_xboole_0(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_317, c_1533])).
% 4.55/1.89  tff(c_1635, plain, (![A_74, B_75]: (k2_xboole_0(A_74, k3_xboole_0(B_75, A_74))=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_317, c_2, c_1575])).
% 4.55/1.89  tff(c_1658, plain, (![B_75]: (k3_xboole_0(B_75, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1635, c_92])).
% 4.55/1.89  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.55/1.89  tff(c_227, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.55/1.89  tff(c_254, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_227])).
% 4.55/1.89  tff(c_1770, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_254])).
% 4.55/1.89  tff(c_18, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.89  tff(c_163, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.55/1.89  tff(c_172, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_163])).
% 4.55/1.89  tff(c_583, plain, (![A_46, B_47]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k4_xboole_0(B_47, A_46))=k5_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.89  tff(c_2244, plain, (![B_85, A_86]: (k2_xboole_0(k4_xboole_0(B_85, A_86), k4_xboole_0(A_86, B_85))=k5_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_2, c_583])).
% 4.55/1.89  tff(c_2299, plain, (![B_4, A_3]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(B_4, A_3), A_3), k4_xboole_0(A_3, B_4))=k5_xboole_0(A_3, k3_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2244])).
% 4.55/1.89  tff(c_3994, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k3_xboole_0(B_117, A_116))=k4_xboole_0(A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1658, c_2, c_1770, c_2, c_18, c_2299])).
% 4.55/1.89  tff(c_4035, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(B_4, A_3))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3994])).
% 4.55/1.89  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.89  tff(c_4448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4035, c_24])).
% 4.55/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.89  
% 4.55/1.89  Inference rules
% 4.55/1.89  ----------------------
% 4.55/1.89  #Ref     : 0
% 4.55/1.89  #Sup     : 1074
% 4.55/1.89  #Fact    : 0
% 4.55/1.89  #Define  : 0
% 4.55/1.89  #Split   : 0
% 4.55/1.89  #Chain   : 0
% 4.55/1.89  #Close   : 0
% 4.55/1.89  
% 4.55/1.89  Ordering : KBO
% 4.55/1.89  
% 4.55/1.89  Simplification rules
% 4.55/1.89  ----------------------
% 4.55/1.89  #Subsume      : 13
% 4.55/1.89  #Demod        : 1303
% 4.55/1.89  #Tautology    : 764
% 4.55/1.89  #SimpNegUnit  : 0
% 4.55/1.89  #BackRed      : 9
% 4.55/1.89  
% 4.55/1.89  #Partial instantiations: 0
% 4.55/1.89  #Strategies tried      : 1
% 4.55/1.89  
% 4.55/1.89  Timing (in seconds)
% 4.55/1.89  ----------------------
% 4.55/1.89  Preprocessing        : 0.29
% 4.55/1.89  Parsing              : 0.16
% 4.55/1.89  CNF conversion       : 0.01
% 4.55/1.89  Main loop            : 0.73
% 4.55/1.89  Inferencing          : 0.21
% 4.55/1.89  Reduction            : 0.36
% 4.55/1.89  Demodulation         : 0.31
% 4.55/1.89  BG Simplification    : 0.03
% 4.55/1.89  Subsumption          : 0.09
% 4.55/1.89  Abstraction          : 0.04
% 4.55/1.89  MUC search           : 0.00
% 4.55/1.89  Cooper               : 0.00
% 4.55/1.89  Total                : 1.05
% 4.55/1.89  Index Insertion      : 0.00
% 4.55/1.89  Index Deletion       : 0.00
% 4.55/1.89  Index Matching       : 0.00
% 4.55/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
