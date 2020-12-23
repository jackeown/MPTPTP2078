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
% DateTime   : Thu Dec  3 09:44:49 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_151,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_151])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = A_49
      | ~ r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_837,plain,(
    ! [A_78,B_79] : k4_xboole_0(k4_xboole_0(A_78,B_79),B_79) = k4_xboole_0(A_78,B_79) ),
    inference(resolution,[status(thm)],[c_22,c_273])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_852,plain,(
    ! [A_78,B_79] : k4_xboole_0(k4_xboole_0(A_78,B_79),k4_xboole_0(A_78,B_79)) = k3_xboole_0(k4_xboole_0(A_78,B_79),B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_18])).

tff(c_917,plain,(
    ! [B_79,A_78] : k3_xboole_0(B_79,k4_xboole_0(A_78,B_79)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_2,c_852])).

tff(c_652,plain,(
    ! [A_70,B_71] : k5_xboole_0(k5_xboole_0(A_70,B_71),k3_xboole_0(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2392,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k5_xboole_0(B_116,k3_xboole_0(A_115,B_116))) = k2_xboole_0(A_115,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_28])).

tff(c_2441,plain,(
    ! [B_79,A_78] : k5_xboole_0(B_79,k5_xboole_0(k4_xboole_0(A_78,B_79),k1_xboole_0)) = k2_xboole_0(B_79,k4_xboole_0(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_2392])).

tff(c_2475,plain,(
    ! [B_79,A_78] : k5_xboole_0(B_79,k4_xboole_0(A_78,B_79)) = k2_xboole_0(B_79,A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_2441])).

tff(c_32,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2475,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.51  
% 3.43/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.51  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.43/1.51  
% 3.43/1.51  %Foreground sorts:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Background operators:
% 3.43/1.51  
% 3.43/1.51  
% 3.43/1.51  %Foreground operators:
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.43/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.43/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.43/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.43/1.51  
% 3.56/1.53  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.56/1.53  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.56/1.53  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.56/1.53  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.56/1.53  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.56/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.56/1.53  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.56/1.53  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.56/1.53  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.56/1.53  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.56/1.53  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.56/1.53  tff(f_60, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.56/1.53  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.53  tff(c_20, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.56/1.53  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.56/1.53  tff(c_58, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.53  tff(c_61, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_58])).
% 3.56/1.53  tff(c_151, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.53  tff(c_158, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_151])).
% 3.56/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.53  tff(c_22, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.53  tff(c_273, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=A_49 | ~r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.53  tff(c_837, plain, (![A_78, B_79]: (k4_xboole_0(k4_xboole_0(A_78, B_79), B_79)=k4_xboole_0(A_78, B_79))), inference(resolution, [status(thm)], [c_22, c_273])).
% 3.56/1.53  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.53  tff(c_852, plain, (![A_78, B_79]: (k4_xboole_0(k4_xboole_0(A_78, B_79), k4_xboole_0(A_78, B_79))=k3_xboole_0(k4_xboole_0(A_78, B_79), B_79))), inference(superposition, [status(thm), theory('equality')], [c_837, c_18])).
% 3.56/1.53  tff(c_917, plain, (![B_79, A_78]: (k3_xboole_0(B_79, k4_xboole_0(A_78, B_79))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_2, c_852])).
% 3.56/1.53  tff(c_652, plain, (![A_70, B_71]: (k5_xboole_0(k5_xboole_0(A_70, B_71), k3_xboole_0(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.53  tff(c_28, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.53  tff(c_2392, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k5_xboole_0(B_116, k3_xboole_0(A_115, B_116)))=k2_xboole_0(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_652, c_28])).
% 3.56/1.53  tff(c_2441, plain, (![B_79, A_78]: (k5_xboole_0(B_79, k5_xboole_0(k4_xboole_0(A_78, B_79), k1_xboole_0))=k2_xboole_0(B_79, k4_xboole_0(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_917, c_2392])).
% 3.56/1.53  tff(c_2475, plain, (![B_79, A_78]: (k5_xboole_0(B_79, k4_xboole_0(A_78, B_79))=k2_xboole_0(B_79, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_2441])).
% 3.56/1.53  tff(c_32, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.53  tff(c_2925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2475, c_32])).
% 3.56/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.53  
% 3.56/1.53  Inference rules
% 3.56/1.53  ----------------------
% 3.56/1.53  #Ref     : 1
% 3.56/1.53  #Sup     : 708
% 3.56/1.53  #Fact    : 0
% 3.56/1.53  #Define  : 0
% 3.56/1.53  #Split   : 0
% 3.56/1.53  #Chain   : 0
% 3.56/1.53  #Close   : 0
% 3.56/1.53  
% 3.56/1.53  Ordering : KBO
% 3.56/1.53  
% 3.56/1.53  Simplification rules
% 3.56/1.53  ----------------------
% 3.56/1.53  #Subsume      : 0
% 3.56/1.53  #Demod        : 672
% 3.56/1.53  #Tautology    : 536
% 3.56/1.53  #SimpNegUnit  : 0
% 3.56/1.53  #BackRed      : 5
% 3.56/1.53  
% 3.56/1.53  #Partial instantiations: 0
% 3.56/1.53  #Strategies tried      : 1
% 3.56/1.53  
% 3.56/1.53  Timing (in seconds)
% 3.56/1.53  ----------------------
% 3.59/1.53  Preprocessing        : 0.26
% 3.59/1.53  Parsing              : 0.15
% 3.59/1.53  CNF conversion       : 0.02
% 3.59/1.53  Main loop            : 0.55
% 3.59/1.53  Inferencing          : 0.19
% 3.59/1.53  Reduction            : 0.23
% 3.59/1.53  Demodulation         : 0.19
% 3.59/1.53  BG Simplification    : 0.02
% 3.59/1.53  Subsumption          : 0.07
% 3.59/1.53  Abstraction          : 0.03
% 3.59/1.53  MUC search           : 0.00
% 3.59/1.53  Cooper               : 0.00
% 3.59/1.53  Total                : 0.83
% 3.59/1.53  Index Insertion      : 0.00
% 3.59/1.53  Index Deletion       : 0.00
% 3.59/1.53  Index Matching       : 0.00
% 3.59/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
