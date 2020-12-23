%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:01 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 101 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   28 (  92 expanded)
%              Number of equality atoms :   27 (  91 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k4_xboole_0(A_20,B_21),C_22) = k4_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_256,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(A_30,k2_xboole_0(k4_xboole_0(A_30,B_31),C_32)) = k4_xboole_0(k3_xboole_0(A_30,B_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_312,plain,(
    ! [A_30,B_2,B_31] : k4_xboole_0(A_30,k2_xboole_0(B_2,k4_xboole_0(A_30,B_31))) = k4_xboole_0(k3_xboole_0(A_30,B_31),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ! [C_27,A_28,B_29] : k2_xboole_0(C_27,k4_xboole_0(A_28,k2_xboole_0(B_29,C_27))) = k2_xboole_0(C_27,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_6])).

tff(c_252,plain,(
    ! [A_1,A_28,B_2] : k2_xboole_0(A_1,k4_xboole_0(A_28,k2_xboole_0(A_1,B_2))) = k2_xboole_0(A_1,k4_xboole_0(A_28,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_1573,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k4_xboole_0(A_59,B_60),k4_xboole_0(A_59,k2_xboole_0(B_60,C_61))) = k3_xboole_0(k4_xboole_0(A_59,B_60),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1597,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(A_59,k2_xboole_0(B_60,k4_xboole_0(A_59,k2_xboole_0(B_60,C_61)))) = k3_xboole_0(k4_xboole_0(A_59,B_60),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_1573,c_8])).

tff(c_1792,plain,(
    ! [A_62,C_63,B_64] : k4_xboole_0(k3_xboole_0(A_62,C_63),B_64) = k3_xboole_0(k4_xboole_0(A_62,B_64),C_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_252,c_1597])).

tff(c_1974,plain,(
    ! [B_65,A_66,B_67] : k4_xboole_0(k3_xboole_0(B_65,A_66),B_67) = k3_xboole_0(k4_xboole_0(A_66,B_67),B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1792])).

tff(c_1752,plain,(
    ! [A_59,C_61,B_60] : k4_xboole_0(k3_xboole_0(A_59,C_61),B_60) = k3_xboole_0(k4_xboole_0(A_59,B_60),C_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_252,c_1597])).

tff(c_2403,plain,(
    ! [B_70,B_71,A_72] : k3_xboole_0(k4_xboole_0(B_70,B_71),A_72) = k3_xboole_0(k4_xboole_0(A_72,B_71),B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_1752])).

tff(c_3091,plain,(
    ! [A_78,B_79,A_80] : k3_xboole_0(k4_xboole_0(A_78,B_79),A_80) = k3_xboole_0(A_78,k4_xboole_0(A_80,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2403])).

tff(c_3216,plain,(
    ! [A_78,A_3,B_79] : k3_xboole_0(A_78,k4_xboole_0(A_3,B_79)) = k3_xboole_0(A_3,k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3091])).

tff(c_12,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_3') != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1789,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_12])).

tff(c_1791,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1789])).

tff(c_5959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3216,c_1791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.65  
% 7.58/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.66  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.58/2.66  
% 7.58/2.66  %Foreground sorts:
% 7.58/2.66  
% 7.58/2.66  
% 7.58/2.66  %Background operators:
% 7.58/2.66  
% 7.58/2.66  
% 7.58/2.66  %Foreground operators:
% 7.58/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.58/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.58/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.58/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.58/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.58/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.58/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.58/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.58/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.58/2.66  
% 7.58/2.67  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.58/2.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.58/2.67  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.58/2.67  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.58/2.67  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.58/2.67  tff(f_38, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.58/2.67  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.58/2.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.58/2.67  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.58/2.67  tff(c_107, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k4_xboole_0(A_20, B_21), C_22)=k4_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.58/2.67  tff(c_256, plain, (![A_30, B_31, C_32]: (k4_xboole_0(A_30, k2_xboole_0(k4_xboole_0(A_30, B_31), C_32))=k4_xboole_0(k3_xboole_0(A_30, B_31), C_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_107])).
% 7.58/2.67  tff(c_312, plain, (![A_30, B_2, B_31]: (k4_xboole_0(A_30, k2_xboole_0(B_2, k4_xboole_0(A_30, B_31)))=k4_xboole_0(k3_xboole_0(A_30, B_31), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 7.58/2.67  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.58/2.67  tff(c_227, plain, (![C_27, A_28, B_29]: (k2_xboole_0(C_27, k4_xboole_0(A_28, k2_xboole_0(B_29, C_27)))=k2_xboole_0(C_27, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_6])).
% 7.58/2.67  tff(c_252, plain, (![A_1, A_28, B_2]: (k2_xboole_0(A_1, k4_xboole_0(A_28, k2_xboole_0(A_1, B_2)))=k2_xboole_0(A_1, k4_xboole_0(A_28, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_227])).
% 7.58/2.67  tff(c_1573, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k4_xboole_0(A_59, B_60), k4_xboole_0(A_59, k2_xboole_0(B_60, C_61)))=k3_xboole_0(k4_xboole_0(A_59, B_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 7.58/2.67  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.58/2.67  tff(c_1597, plain, (![A_59, B_60, C_61]: (k4_xboole_0(A_59, k2_xboole_0(B_60, k4_xboole_0(A_59, k2_xboole_0(B_60, C_61))))=k3_xboole_0(k4_xboole_0(A_59, B_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_1573, c_8])).
% 7.58/2.67  tff(c_1792, plain, (![A_62, C_63, B_64]: (k4_xboole_0(k3_xboole_0(A_62, C_63), B_64)=k3_xboole_0(k4_xboole_0(A_62, B_64), C_63))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_252, c_1597])).
% 7.58/2.67  tff(c_1974, plain, (![B_65, A_66, B_67]: (k4_xboole_0(k3_xboole_0(B_65, A_66), B_67)=k3_xboole_0(k4_xboole_0(A_66, B_67), B_65))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1792])).
% 7.58/2.67  tff(c_1752, plain, (![A_59, C_61, B_60]: (k4_xboole_0(k3_xboole_0(A_59, C_61), B_60)=k3_xboole_0(k4_xboole_0(A_59, B_60), C_61))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_252, c_1597])).
% 7.58/2.67  tff(c_2403, plain, (![B_70, B_71, A_72]: (k3_xboole_0(k4_xboole_0(B_70, B_71), A_72)=k3_xboole_0(k4_xboole_0(A_72, B_71), B_70))), inference(superposition, [status(thm), theory('equality')], [c_1974, c_1752])).
% 7.58/2.67  tff(c_3091, plain, (![A_78, B_79, A_80]: (k3_xboole_0(k4_xboole_0(A_78, B_79), A_80)=k3_xboole_0(A_78, k4_xboole_0(A_80, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2403])).
% 7.58/2.67  tff(c_3216, plain, (![A_78, A_3, B_79]: (k3_xboole_0(A_78, k4_xboole_0(A_3, B_79))=k3_xboole_0(A_3, k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3091])).
% 7.58/2.67  tff(c_12, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_3')!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.58/2.67  tff(c_1789, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_12])).
% 7.58/2.67  tff(c_1791, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1789])).
% 7.58/2.67  tff(c_5959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3216, c_1791])).
% 7.58/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/2.67  
% 7.58/2.67  Inference rules
% 7.58/2.67  ----------------------
% 7.58/2.67  #Ref     : 0
% 7.58/2.67  #Sup     : 1542
% 7.58/2.67  #Fact    : 0
% 7.58/2.67  #Define  : 0
% 7.58/2.67  #Split   : 0
% 7.58/2.67  #Chain   : 0
% 7.58/2.67  #Close   : 0
% 7.58/2.67  
% 7.58/2.67  Ordering : KBO
% 7.58/2.67  
% 7.58/2.67  Simplification rules
% 7.58/2.67  ----------------------
% 7.58/2.67  #Subsume      : 107
% 7.58/2.67  #Demod        : 1230
% 7.58/2.67  #Tautology    : 259
% 7.58/2.67  #SimpNegUnit  : 0
% 7.58/2.67  #BackRed      : 9
% 7.58/2.67  
% 7.58/2.67  #Partial instantiations: 0
% 7.58/2.67  #Strategies tried      : 1
% 7.58/2.67  
% 7.58/2.67  Timing (in seconds)
% 7.58/2.67  ----------------------
% 7.58/2.67  Preprocessing        : 0.27
% 7.58/2.67  Parsing              : 0.15
% 7.82/2.67  CNF conversion       : 0.01
% 7.82/2.67  Main loop            : 1.64
% 7.82/2.67  Inferencing          : 0.40
% 7.82/2.67  Reduction            : 0.91
% 7.82/2.67  Demodulation         : 0.82
% 7.82/2.67  BG Simplification    : 0.07
% 7.82/2.67  Subsumption          : 0.18
% 7.82/2.67  Abstraction          : 0.10
% 7.82/2.67  MUC search           : 0.00
% 7.82/2.67  Cooper               : 0.00
% 7.82/2.67  Total                : 1.94
% 7.82/2.67  Index Insertion      : 0.00
% 7.82/2.67  Index Deletion       : 0.00
% 7.82/2.67  Index Matching       : 0.00
% 7.82/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
