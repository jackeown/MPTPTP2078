%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:28 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 119 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 116 expanded)
%              Number of equality atoms :   36 (  93 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_25,A_26] : k5_xboole_0(B_25,A_26) = k5_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [A_26] : k5_xboole_0(k1_xboole_0,A_26) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_460,plain,(
    ! [A_44,B_45,C_46] : k5_xboole_0(k5_xboole_0(A_44,B_45),C_46) = k5_xboole_0(A_44,k5_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_517,plain,(
    ! [A_18,C_46] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_46)) = k5_xboole_0(k1_xboole_0,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_460])).

tff(c_631,plain,(
    ! [A_52,C_53] : k5_xboole_0(A_52,k5_xboole_0(A_52,C_53)) = C_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_517])).

tff(c_3511,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_631])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_180,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_180])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1496,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(B_83,A_82)) = k4_xboole_0(A_82,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_1546,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_1496])).

tff(c_535,plain,(
    ! [A_18,C_46] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_46)) = C_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_517])).

tff(c_1699,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1546,c_535])).

tff(c_3534,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3511,c_1699])).

tff(c_4228,plain,(
    ! [A_121,B_122,C_123] : k5_xboole_0(A_121,k5_xboole_0(k3_xboole_0(A_121,B_122),C_123)) = k5_xboole_0(k4_xboole_0(A_121,B_122),C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_460])).

tff(c_4411,plain,(
    ! [A_121,B_122] : k5_xboole_0(k4_xboole_0(A_121,B_122),k3_xboole_0(A_121,B_122)) = k5_xboole_0(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4228])).

tff(c_4440,plain,(
    ! [A_124,B_125] : k5_xboole_0(k4_xboole_0(A_124,B_125),k3_xboole_0(A_124,B_125)) = A_124 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4411])).

tff(c_4475,plain,(
    ! [A_124,B_125] : k5_xboole_0(k4_xboole_0(A_124,B_125),A_124) = k3_xboole_0(A_124,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_4440,c_535])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_786,plain,(
    ! [A_62,B_63] : k3_xboole_0(k4_xboole_0(A_62,B_63),A_62) = k4_xboole_0(A_62,B_63) ),
    inference(resolution,[status(thm)],[c_14,c_180])).

tff(c_835,plain,(
    ! [B_2,B_63] : k3_xboole_0(B_2,k4_xboole_0(B_2,B_63)) = k4_xboole_0(B_2,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_786])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_674,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_631])).

tff(c_5856,plain,(
    ! [A_140,B_141] : k5_xboole_0(k3_xboole_0(A_140,B_141),A_140) = k4_xboole_0(A_140,B_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_4440,c_674])).

tff(c_5951,plain,(
    ! [B_2,B_63] : k5_xboole_0(k4_xboole_0(B_2,B_63),B_2) = k4_xboole_0(B_2,k4_xboole_0(B_2,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_5856])).

tff(c_6678,plain,(
    ! [B_145,B_146] : k4_xboole_0(B_145,k4_xboole_0(B_145,B_146)) = k3_xboole_0(B_145,B_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4475,c_5951])).

tff(c_195,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_tarski(A_30,k4_xboole_0(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [B_31,C_32,B_13] : r1_tarski(k4_xboole_0(k4_xboole_0(B_31,C_32),B_13),B_31) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_7356,plain,(
    ! [B_165,B_166,B_167] : r1_tarski(k4_xboole_0(k3_xboole_0(B_165,B_166),B_167),B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_6678,c_200])).

tff(c_7383,plain,(
    ! [B_167] : r1_tarski(k4_xboole_0('#skF_1',B_167),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3534,c_7356])).

tff(c_22,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7383,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:32:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  
% 6.21/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.21/2.27  
% 6.21/2.27  %Foreground sorts:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Background operators:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Foreground operators:
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.21/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.21/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.21/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.21/2.27  
% 6.21/2.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.21/2.29  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.21/2.29  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.21/2.29  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.21/2.29  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.21/2.29  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 6.21/2.29  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.21/2.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.21/2.29  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.21/2.29  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.21/2.29  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.29  tff(c_85, plain, (![B_25, A_26]: (k5_xboole_0(B_25, A_26)=k5_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.21/2.29  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.21/2.29  tff(c_101, plain, (![A_26]: (k5_xboole_0(k1_xboole_0, A_26)=A_26)), inference(superposition, [status(thm), theory('equality')], [c_85, c_16])).
% 6.21/2.29  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.29  tff(c_460, plain, (![A_44, B_45, C_46]: (k5_xboole_0(k5_xboole_0(A_44, B_45), C_46)=k5_xboole_0(A_44, k5_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.21/2.29  tff(c_517, plain, (![A_18, C_46]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_46))=k5_xboole_0(k1_xboole_0, C_46))), inference(superposition, [status(thm), theory('equality')], [c_20, c_460])).
% 6.21/2.29  tff(c_631, plain, (![A_52, C_53]: (k5_xboole_0(A_52, k5_xboole_0(A_52, C_53))=C_53)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_517])).
% 6.21/2.29  tff(c_3511, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k3_xboole_0(A_112, B_113))), inference(superposition, [status(thm), theory('equality')], [c_6, c_631])).
% 6.21/2.29  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.21/2.29  tff(c_180, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.21/2.29  tff(c_188, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_24, c_180])).
% 6.21/2.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.21/2.29  tff(c_211, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.29  tff(c_1496, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(B_83, A_82))=k4_xboole_0(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 6.21/2.29  tff(c_1546, plain, (k5_xboole_0('#skF_2', '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_188, c_1496])).
% 6.21/2.29  tff(c_535, plain, (![A_18, C_46]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_46))=C_46)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_517])).
% 6.21/2.29  tff(c_1699, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1546, c_535])).
% 6.21/2.29  tff(c_3534, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3511, c_1699])).
% 6.21/2.29  tff(c_4228, plain, (![A_121, B_122, C_123]: (k5_xboole_0(A_121, k5_xboole_0(k3_xboole_0(A_121, B_122), C_123))=k5_xboole_0(k4_xboole_0(A_121, B_122), C_123))), inference(superposition, [status(thm), theory('equality')], [c_6, c_460])).
% 6.21/2.29  tff(c_4411, plain, (![A_121, B_122]: (k5_xboole_0(k4_xboole_0(A_121, B_122), k3_xboole_0(A_121, B_122))=k5_xboole_0(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4228])).
% 6.21/2.29  tff(c_4440, plain, (![A_124, B_125]: (k5_xboole_0(k4_xboole_0(A_124, B_125), k3_xboole_0(A_124, B_125))=A_124)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4411])).
% 6.21/2.29  tff(c_4475, plain, (![A_124, B_125]: (k5_xboole_0(k4_xboole_0(A_124, B_125), A_124)=k3_xboole_0(A_124, B_125))), inference(superposition, [status(thm), theory('equality')], [c_4440, c_535])).
% 6.21/2.29  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.21/2.29  tff(c_786, plain, (![A_62, B_63]: (k3_xboole_0(k4_xboole_0(A_62, B_63), A_62)=k4_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_14, c_180])).
% 6.21/2.29  tff(c_835, plain, (![B_2, B_63]: (k3_xboole_0(B_2, k4_xboole_0(B_2, B_63))=k4_xboole_0(B_2, B_63))), inference(superposition, [status(thm), theory('equality')], [c_2, c_786])).
% 6.21/2.29  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.21/2.29  tff(c_674, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_631])).
% 6.21/2.29  tff(c_5856, plain, (![A_140, B_141]: (k5_xboole_0(k3_xboole_0(A_140, B_141), A_140)=k4_xboole_0(A_140, B_141))), inference(superposition, [status(thm), theory('equality')], [c_4440, c_674])).
% 6.21/2.29  tff(c_5951, plain, (![B_2, B_63]: (k5_xboole_0(k4_xboole_0(B_2, B_63), B_2)=k4_xboole_0(B_2, k4_xboole_0(B_2, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_835, c_5856])).
% 6.21/2.29  tff(c_6678, plain, (![B_145, B_146]: (k4_xboole_0(B_145, k4_xboole_0(B_145, B_146))=k3_xboole_0(B_145, B_146))), inference(demodulation, [status(thm), theory('equality')], [c_4475, c_5951])).
% 6.21/2.29  tff(c_195, plain, (![A_30, B_31, C_32]: (r1_tarski(A_30, B_31) | ~r1_tarski(A_30, k4_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.21/2.29  tff(c_200, plain, (![B_31, C_32, B_13]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_31, C_32), B_13), B_31))), inference(resolution, [status(thm)], [c_14, c_195])).
% 6.21/2.29  tff(c_7356, plain, (![B_165, B_166, B_167]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_165, B_166), B_167), B_165))), inference(superposition, [status(thm), theory('equality')], [c_6678, c_200])).
% 6.21/2.29  tff(c_7383, plain, (![B_167]: (r1_tarski(k4_xboole_0('#skF_1', B_167), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3534, c_7356])).
% 6.21/2.29  tff(c_22, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.21/2.29  tff(c_7432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7383, c_22])).
% 6.21/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.29  
% 6.21/2.29  Inference rules
% 6.21/2.29  ----------------------
% 6.21/2.29  #Ref     : 0
% 6.21/2.29  #Sup     : 1833
% 6.21/2.29  #Fact    : 0
% 6.21/2.29  #Define  : 0
% 6.21/2.29  #Split   : 0
% 6.21/2.29  #Chain   : 0
% 6.21/2.29  #Close   : 0
% 6.21/2.29  
% 6.21/2.29  Ordering : KBO
% 6.21/2.29  
% 6.21/2.29  Simplification rules
% 6.21/2.29  ----------------------
% 6.21/2.29  #Subsume      : 68
% 6.21/2.29  #Demod        : 2214
% 6.21/2.29  #Tautology    : 1110
% 6.21/2.29  #SimpNegUnit  : 0
% 6.21/2.29  #BackRed      : 16
% 6.21/2.29  
% 6.21/2.29  #Partial instantiations: 0
% 6.21/2.29  #Strategies tried      : 1
% 6.21/2.29  
% 6.21/2.29  Timing (in seconds)
% 6.21/2.29  ----------------------
% 6.21/2.29  Preprocessing        : 0.26
% 6.21/2.29  Parsing              : 0.14
% 6.21/2.29  CNF conversion       : 0.02
% 6.21/2.29  Main loop            : 1.26
% 6.21/2.29  Inferencing          : 0.32
% 6.21/2.29  Reduction            : 0.67
% 6.21/2.29  Demodulation         : 0.59
% 6.21/2.29  BG Simplification    : 0.05
% 6.21/2.29  Subsumption          : 0.15
% 6.21/2.29  Abstraction          : 0.05
% 6.21/2.29  MUC search           : 0.00
% 6.21/2.29  Cooper               : 0.00
% 6.21/2.29  Total                : 1.55
% 6.21/2.29  Index Insertion      : 0.00
% 6.21/2.29  Index Deletion       : 0.00
% 6.21/2.29  Index Matching       : 0.00
% 6.21/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
