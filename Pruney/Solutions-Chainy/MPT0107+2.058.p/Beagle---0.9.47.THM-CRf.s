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
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_830,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_219,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_240,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_219])).

tff(c_243,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_240])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_237,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k5_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_219])).

tff(c_692,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_237])).

tff(c_831,plain,(
    ! [A_66,B_67] : k3_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_843,plain,(
    ! [A_66,B_67] : k4_xboole_0(k2_xboole_0(A_66,k4_xboole_0(A_66,B_67)),k4_xboole_0(A_66,B_67)) = k5_xboole_0(A_66,k4_xboole_0(A_66,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_6])).

tff(c_943,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_692,c_843])).

tff(c_992,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_943])).

tff(c_1012,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_992])).

tff(c_20,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:25:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  
% 2.43/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.33  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.43/1.33  
% 2.43/1.33  %Foreground sorts:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Background operators:
% 2.43/1.33  
% 2.43/1.33  
% 2.43/1.33  %Foreground operators:
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.33  
% 2.43/1.34  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.43/1.34  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.43/1.34  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.43/1.34  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.43/1.34  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.43/1.34  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.43/1.34  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.43/1.34  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.43/1.34  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.43/1.34  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.34  tff(c_90, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.34  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.34  tff(c_93, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, k4_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_14])).
% 2.43/1.34  tff(c_830, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_93])).
% 2.43/1.34  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.34  tff(c_16, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.34  tff(c_219, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.34  tff(c_240, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_219])).
% 2.43/1.34  tff(c_243, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_240])).
% 2.43/1.34  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.34  tff(c_41, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.34  tff(c_50, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_41])).
% 2.43/1.34  tff(c_237, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k5_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_219])).
% 2.43/1.34  tff(c_692, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_237])).
% 2.43/1.34  tff(c_831, plain, (![A_66, B_67]: (k3_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_93])).
% 2.43/1.34  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.34  tff(c_843, plain, (![A_66, B_67]: (k4_xboole_0(k2_xboole_0(A_66, k4_xboole_0(A_66, B_67)), k4_xboole_0(A_66, B_67))=k5_xboole_0(A_66, k4_xboole_0(A_66, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_831, c_6])).
% 2.43/1.34  tff(c_943, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_692, c_843])).
% 2.43/1.34  tff(c_992, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k3_xboole_0(A_10, k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_943])).
% 2.43/1.34  tff(c_1012, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_992])).
% 2.43/1.34  tff(c_20, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.43/1.34  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1012, c_20])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 0
% 2.43/1.34  #Sup     : 260
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 0
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 0
% 2.43/1.34  #Demod        : 242
% 2.43/1.34  #Tautology    : 210
% 2.43/1.34  #SimpNegUnit  : 0
% 2.43/1.34  #BackRed      : 3
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.34  Preprocessing        : 0.27
% 2.43/1.34  Parsing              : 0.15
% 2.43/1.34  CNF conversion       : 0.02
% 2.43/1.34  Main loop            : 0.33
% 2.43/1.34  Inferencing          : 0.13
% 2.43/1.34  Reduction            : 0.12
% 2.43/1.34  Demodulation         : 0.09
% 2.43/1.34  BG Simplification    : 0.01
% 2.43/1.34  Subsumption          : 0.04
% 2.43/1.34  Abstraction          : 0.02
% 2.43/1.35  MUC search           : 0.00
% 2.43/1.35  Cooper               : 0.00
% 2.43/1.35  Total                : 0.62
% 2.43/1.35  Index Insertion      : 0.00
% 2.43/1.35  Index Deletion       : 0.00
% 2.43/1.35  Index Matching       : 0.00
% 2.43/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
