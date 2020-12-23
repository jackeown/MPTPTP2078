%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  43 expanded)
%              Number of equality atoms :   34 (  38 expanded)
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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_162,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_315,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_343,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_315])).

tff(c_359,plain,(
    ! [A_5,B_6] : k3_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k4_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_343])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [B_25,A_26] : k5_xboole_0(B_25,A_26) = k5_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_14])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_493,plain,(
    ! [A_48,B_49,C_50] : k5_xboole_0(k5_xboole_0(A_48,B_49),C_50) = k5_xboole_0(A_48,k5_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_570,plain,(
    ! [A_14,C_50] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_50)) = k5_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_493])).

tff(c_636,plain,(
    ! [A_54,C_55] : k5_xboole_0(A_54,k5_xboole_0(A_54,C_55)) = C_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_570])).

tff(c_675,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k4_xboole_0(B_18,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_636])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1431,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(B_77,k5_xboole_0(A_76,C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_493])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(k5_xboole_0(A_15,B_16),k2_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1482,plain,(
    ! [B_77,A_76] : k5_xboole_0(B_77,k5_xboole_0(A_76,k2_xboole_0(A_76,B_77))) = k3_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_20])).

tff(c_1616,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,k4_xboole_0(B_79,A_80)) = k3_xboole_0(A_80,B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_1482])).

tff(c_1673,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1616])).

tff(c_1700,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_1673])).

tff(c_24,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.67  
% 3.34/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.67  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.34/1.67  
% 3.34/1.67  %Foreground sorts:
% 3.34/1.67  
% 3.34/1.67  
% 3.34/1.67  %Background operators:
% 3.34/1.67  
% 3.34/1.67  
% 3.34/1.67  %Foreground operators:
% 3.34/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.67  
% 3.34/1.68  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.34/1.68  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.34/1.68  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.34/1.68  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.68  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.34/1.68  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.34/1.68  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.68  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.34/1.68  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.34/1.68  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.34/1.68  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.68  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.68  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.68  tff(c_162, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.68  tff(c_170, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_162])).
% 3.34/1.68  tff(c_315, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.68  tff(c_343, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_170, c_315])).
% 3.34/1.68  tff(c_359, plain, (![A_5, B_6]: (k3_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k4_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_343])).
% 3.34/1.68  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.68  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.68  tff(c_65, plain, (![B_25, A_26]: (k5_xboole_0(B_25, A_26)=k5_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.68  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.68  tff(c_81, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_65, c_14])).
% 3.34/1.68  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.68  tff(c_493, plain, (![A_48, B_49, C_50]: (k5_xboole_0(k5_xboole_0(A_48, B_49), C_50)=k5_xboole_0(A_48, k5_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.68  tff(c_570, plain, (![A_14, C_50]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_50))=k5_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_18, c_493])).
% 3.34/1.68  tff(c_636, plain, (![A_54, C_55]: (k5_xboole_0(A_54, k5_xboole_0(A_54, C_55))=C_55)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_570])).
% 3.34/1.68  tff(c_675, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k4_xboole_0(B_18, A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_636])).
% 3.34/1.68  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.68  tff(c_1431, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(B_77, k5_xboole_0(A_76, C_78)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_493])).
% 3.34/1.68  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(A_15, B_16), k2_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.68  tff(c_1482, plain, (![B_77, A_76]: (k5_xboole_0(B_77, k5_xboole_0(A_76, k2_xboole_0(A_76, B_77)))=k3_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_1431, c_20])).
% 3.34/1.68  tff(c_1616, plain, (![B_79, A_80]: (k5_xboole_0(B_79, k4_xboole_0(B_79, A_80))=k3_xboole_0(A_80, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_675, c_1482])).
% 3.34/1.68  tff(c_1673, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k3_xboole_0(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1616])).
% 3.34/1.68  tff(c_1700, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_1673])).
% 3.34/1.68  tff(c_24, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.68  tff(c_1932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1700, c_24])).
% 3.34/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.68  
% 3.34/1.68  Inference rules
% 3.34/1.68  ----------------------
% 3.34/1.68  #Ref     : 0
% 3.34/1.68  #Sup     : 469
% 3.34/1.68  #Fact    : 0
% 3.34/1.68  #Define  : 0
% 3.34/1.68  #Split   : 0
% 3.34/1.68  #Chain   : 0
% 3.34/1.68  #Close   : 0
% 3.34/1.68  
% 3.34/1.68  Ordering : KBO
% 3.34/1.68  
% 3.34/1.68  Simplification rules
% 3.34/1.68  ----------------------
% 3.34/1.68  #Subsume      : 6
% 3.34/1.68  #Demod        : 345
% 3.34/1.68  #Tautology    : 317
% 3.34/1.68  #SimpNegUnit  : 0
% 3.34/1.68  #BackRed      : 2
% 3.34/1.68  
% 3.34/1.68  #Partial instantiations: 0
% 3.34/1.68  #Strategies tried      : 1
% 3.34/1.68  
% 3.34/1.68  Timing (in seconds)
% 3.34/1.68  ----------------------
% 3.34/1.69  Preprocessing        : 0.28
% 3.34/1.69  Parsing              : 0.16
% 3.34/1.69  CNF conversion       : 0.02
% 3.34/1.69  Main loop            : 0.62
% 3.34/1.69  Inferencing          : 0.22
% 3.34/1.69  Reduction            : 0.27
% 3.34/1.69  Demodulation         : 0.23
% 3.34/1.69  BG Simplification    : 0.03
% 3.34/1.69  Subsumption          : 0.07
% 3.34/1.69  Abstraction          : 0.03
% 3.34/1.69  MUC search           : 0.00
% 3.34/1.69  Cooper               : 0.00
% 3.34/1.69  Total                : 0.93
% 3.34/1.69  Index Insertion      : 0.00
% 3.34/1.69  Index Deletion       : 0.00
% 3.34/1.69  Index Matching       : 0.00
% 3.34/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
