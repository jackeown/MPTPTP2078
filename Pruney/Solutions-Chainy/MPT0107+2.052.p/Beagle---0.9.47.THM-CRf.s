%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   38 (  70 expanded)
%              Number of equality atoms :   29 (  42 expanded)
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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_30])).

tff(c_39,plain,(
    ! [A_21,B_22] : k4_xboole_0(k4_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_30])).

tff(c_84,plain,(
    ! [A_27,B_28] : r1_tarski(k1_xboole_0,k4_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_8])).

tff(c_91,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_132,plain,(
    ! [A_31,B_32] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_31,B_32)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_39])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [B_32] : k3_xboole_0(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_12])).

tff(c_221,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_246,plain,(
    ! [B_32] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_221])).

tff(c_257,plain,(
    ! [B_38] : k4_xboole_0(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_246])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_266,plain,(
    ! [B_38] : k5_xboole_0(B_38,k1_xboole_0) = k2_xboole_0(B_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_16])).

tff(c_294,plain,(
    ! [B_38] : k2_xboole_0(B_38,k1_xboole_0) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_266])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_25,B_26] : r1_tarski(k3_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_83,plain,(
    ! [A_25,B_26] : k4_xboole_0(k3_xboole_0(A_25,B_26),A_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_6])).

tff(c_371,plain,(
    ! [A_44,B_45] : k2_xboole_0(k4_xboole_0(A_44,B_45),k4_xboole_0(B_45,A_44)) = k5_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_383,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)),k1_xboole_0) = k5_xboole_0(A_25,k3_xboole_0(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_371])).

tff(c_411,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_10,c_383])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.55  
% 2.38/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.56  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.38/1.56  
% 2.38/1.56  %Foreground sorts:
% 2.38/1.56  
% 2.38/1.56  
% 2.38/1.56  %Background operators:
% 2.38/1.56  
% 2.38/1.56  
% 2.38/1.56  %Foreground operators:
% 2.38/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.38/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.56  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.56  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.56  
% 2.38/1.57  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.38/1.57  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.38/1.57  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.38/1.57  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.38/1.57  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.38/1.57  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.38/1.57  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.38/1.57  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.38/1.57  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.57  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.57  tff(c_30, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.57  tff(c_38, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_30])).
% 2.38/1.57  tff(c_39, plain, (![A_21, B_22]: (k4_xboole_0(k4_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_30])).
% 2.38/1.57  tff(c_84, plain, (![A_27, B_28]: (r1_tarski(k1_xboole_0, k4_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_8])).
% 2.38/1.57  tff(c_91, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_84])).
% 2.38/1.57  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.57  tff(c_96, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_6])).
% 2.38/1.57  tff(c_132, plain, (![A_31, B_32]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_31, B_32))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_39])).
% 2.38/1.57  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.57  tff(c_145, plain, (![B_32]: (k3_xboole_0(k1_xboole_0, B_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_12])).
% 2.38/1.57  tff(c_221, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.57  tff(c_246, plain, (![B_32]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_32))), inference(superposition, [status(thm), theory('equality')], [c_145, c_221])).
% 2.38/1.57  tff(c_257, plain, (![B_38]: (k4_xboole_0(k1_xboole_0, B_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_246])).
% 2.38/1.57  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.38/1.57  tff(c_266, plain, (![B_38]: (k5_xboole_0(B_38, k1_xboole_0)=k2_xboole_0(B_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_257, c_16])).
% 2.38/1.57  tff(c_294, plain, (![B_38]: (k2_xboole_0(B_38, k1_xboole_0)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_266])).
% 2.38/1.57  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.57  tff(c_55, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.57  tff(c_79, plain, (![A_25, B_26]: (r1_tarski(k3_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 2.38/1.57  tff(c_83, plain, (![A_25, B_26]: (k4_xboole_0(k3_xboole_0(A_25, B_26), A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_6])).
% 2.38/1.57  tff(c_371, plain, (![A_44, B_45]: (k2_xboole_0(k4_xboole_0(A_44, B_45), k4_xboole_0(B_45, A_44))=k5_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.57  tff(c_383, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, k3_xboole_0(A_25, B_26)), k1_xboole_0)=k5_xboole_0(A_25, k3_xboole_0(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_371])).
% 2.38/1.57  tff(c_411, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_10, c_383])).
% 2.38/1.57  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.57  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_411, c_18])).
% 2.38/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.57  
% 2.38/1.57  Inference rules
% 2.38/1.57  ----------------------
% 2.38/1.57  #Ref     : 0
% 2.38/1.57  #Sup     : 205
% 2.38/1.57  #Fact    : 0
% 2.38/1.57  #Define  : 0
% 2.38/1.57  #Split   : 0
% 2.38/1.57  #Chain   : 0
% 2.38/1.57  #Close   : 0
% 2.38/1.57  
% 2.38/1.57  Ordering : KBO
% 2.38/1.57  
% 2.38/1.57  Simplification rules
% 2.38/1.57  ----------------------
% 2.38/1.57  #Subsume      : 0
% 2.38/1.57  #Demod        : 160
% 2.38/1.57  #Tautology    : 172
% 2.38/1.57  #SimpNegUnit  : 0
% 2.38/1.57  #BackRed      : 1
% 2.38/1.57  
% 2.38/1.57  #Partial instantiations: 0
% 2.38/1.57  #Strategies tried      : 1
% 2.38/1.57  
% 2.38/1.57  Timing (in seconds)
% 2.38/1.57  ----------------------
% 2.38/1.57  Preprocessing        : 0.37
% 2.38/1.57  Parsing              : 0.22
% 2.38/1.57  CNF conversion       : 0.02
% 2.38/1.57  Main loop            : 0.30
% 2.38/1.57  Inferencing          : 0.12
% 2.38/1.57  Reduction            : 0.11
% 2.38/1.57  Demodulation         : 0.08
% 2.38/1.57  BG Simplification    : 0.02
% 2.38/1.57  Subsumption          : 0.04
% 2.38/1.57  Abstraction          : 0.02
% 2.38/1.57  MUC search           : 0.00
% 2.38/1.57  Cooper               : 0.00
% 2.38/1.57  Total                : 0.69
% 2.38/1.57  Index Insertion      : 0.00
% 2.38/1.57  Index Deletion       : 0.00
% 2.38/1.57  Index Matching       : 0.00
% 2.38/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
