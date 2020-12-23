%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_101,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_109,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_54])).

tff(c_22,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_15,B_16] : k3_xboole_0(k4_xboole_0(A_15,B_16),B_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_233,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k3_xboole_0(A_40,B_41),C_42) = k3_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_356,plain,(
    ! [A_47,B_48,C_49] : r1_xboole_0(k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)),C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_20])).

tff(c_394,plain,(
    ! [C_50] : r1_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_356])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_467,plain,(
    ! [C_53] : k3_xboole_0(k1_xboole_0,C_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_394,c_4])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_481,plain,(
    ! [C_53] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_12])).

tff(c_508,plain,(
    ! [C_53] : k4_xboole_0(k1_xboole_0,C_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_481])).

tff(c_260,plain,(
    ! [A_15,B_16,C_42] : k3_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(B_16,C_42)) = k4_xboole_0(k1_xboole_0,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_233])).

tff(c_4272,plain,(
    ! [A_129,B_130,C_131] : k3_xboole_0(k4_xboole_0(A_129,B_130),k4_xboole_0(B_130,C_131)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_260])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_930,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(B_65,k4_xboole_0(A_64,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_1048,plain,(
    ! [C_68] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_68)) = k4_xboole_0('#skF_1',C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_930])).

tff(c_1100,plain,(
    ! [C_68] : k3_xboole_0(k4_xboole_0('#skF_1',C_68),k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1048])).

tff(c_4299,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4272,c_1100])).

tff(c_4447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_4299])).

tff(c_4448,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_4511,plain,(
    ! [A_138,B_139] :
      ( k3_xboole_0(A_138,B_139) = A_138
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4519,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_4511])).

tff(c_4705,plain,(
    ! [A_150,B_151,C_152] : k4_xboole_0(k3_xboole_0(A_150,B_151),C_152) = k3_xboole_0(A_150,k4_xboole_0(B_151,C_152)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4886,plain,(
    ! [A_157,B_158,C_159] : r1_xboole_0(k3_xboole_0(A_157,k4_xboole_0(B_158,C_159)),C_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_4705,c_20])).

tff(c_4916,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4519,c_4886])).

tff(c_4933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4448,c_4916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.90  
% 4.58/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.90  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.58/1.90  
% 4.58/1.90  %Foreground sorts:
% 4.58/1.90  
% 4.58/1.90  
% 4.58/1.90  %Background operators:
% 4.58/1.90  
% 4.58/1.90  
% 4.58/1.90  %Foreground operators:
% 4.58/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.58/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.58/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.58/1.90  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.58/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.58/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.58/1.91  
% 4.58/1.92  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.58/1.92  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.58/1.92  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.58/1.92  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.58/1.92  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.58/1.92  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.58/1.92  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.58/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.58/1.92  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.58/1.92  tff(c_101, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.58/1.92  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.58/1.92  tff(c_54, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 4.58/1.92  tff(c_109, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_54])).
% 4.58/1.92  tff(c_22, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.58/1.92  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.58/1.92  tff(c_123, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.92  tff(c_135, plain, (![A_15, B_16]: (k3_xboole_0(k4_xboole_0(A_15, B_16), B_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_123])).
% 4.58/1.92  tff(c_233, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k3_xboole_0(A_40, B_41), C_42)=k3_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.92  tff(c_356, plain, (![A_47, B_48, C_49]: (r1_xboole_0(k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)), C_49))), inference(superposition, [status(thm), theory('equality')], [c_233, c_20])).
% 4.58/1.92  tff(c_394, plain, (![C_50]: (r1_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_135, c_356])).
% 4.58/1.92  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.58/1.92  tff(c_467, plain, (![C_53]: (k3_xboole_0(k1_xboole_0, C_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_394, c_4])).
% 4.58/1.92  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.58/1.92  tff(c_481, plain, (![C_53]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, C_53))), inference(superposition, [status(thm), theory('equality')], [c_467, c_12])).
% 4.58/1.92  tff(c_508, plain, (![C_53]: (k4_xboole_0(k1_xboole_0, C_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_481])).
% 4.58/1.92  tff(c_260, plain, (![A_15, B_16, C_42]: (k3_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(B_16, C_42))=k4_xboole_0(k1_xboole_0, C_42))), inference(superposition, [status(thm), theory('equality')], [c_135, c_233])).
% 4.58/1.92  tff(c_4272, plain, (![A_129, B_130, C_131]: (k3_xboole_0(k4_xboole_0(A_129, B_130), k4_xboole_0(B_130, C_131))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_508, c_260])).
% 4.58/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.58/1.92  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.58/1.92  tff(c_110, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.92  tff(c_118, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_110])).
% 4.58/1.92  tff(c_930, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(B_65, k4_xboole_0(A_64, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_233])).
% 4.58/1.92  tff(c_1048, plain, (![C_68]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_68))=k4_xboole_0('#skF_1', C_68))), inference(superposition, [status(thm), theory('equality')], [c_118, c_930])).
% 4.58/1.92  tff(c_1100, plain, (![C_68]: (k3_xboole_0(k4_xboole_0('#skF_1', C_68), k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', C_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1048])).
% 4.58/1.92  tff(c_4299, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4272, c_1100])).
% 4.58/1.92  tff(c_4447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_4299])).
% 4.58/1.92  tff(c_4448, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 4.58/1.92  tff(c_4511, plain, (![A_138, B_139]: (k3_xboole_0(A_138, B_139)=A_138 | ~r1_tarski(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.58/1.92  tff(c_4519, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_4511])).
% 4.58/1.92  tff(c_4705, plain, (![A_150, B_151, C_152]: (k4_xboole_0(k3_xboole_0(A_150, B_151), C_152)=k3_xboole_0(A_150, k4_xboole_0(B_151, C_152)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.58/1.92  tff(c_4886, plain, (![A_157, B_158, C_159]: (r1_xboole_0(k3_xboole_0(A_157, k4_xboole_0(B_158, C_159)), C_159))), inference(superposition, [status(thm), theory('equality')], [c_4705, c_20])).
% 4.58/1.92  tff(c_4916, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4519, c_4886])).
% 4.58/1.92  tff(c_4933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4448, c_4916])).
% 4.58/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.92  
% 4.58/1.92  Inference rules
% 4.58/1.92  ----------------------
% 4.58/1.92  #Ref     : 0
% 4.58/1.92  #Sup     : 1311
% 4.58/1.92  #Fact    : 0
% 4.58/1.92  #Define  : 0
% 4.58/1.92  #Split   : 1
% 4.58/1.92  #Chain   : 0
% 4.58/1.92  #Close   : 0
% 4.58/1.92  
% 4.58/1.92  Ordering : KBO
% 4.58/1.92  
% 4.58/1.92  Simplification rules
% 4.58/1.92  ----------------------
% 4.58/1.92  #Subsume      : 2
% 4.58/1.92  #Demod        : 962
% 4.58/1.92  #Tautology    : 949
% 4.58/1.92  #SimpNegUnit  : 2
% 4.58/1.92  #BackRed      : 1
% 4.58/1.92  
% 4.58/1.92  #Partial instantiations: 0
% 4.58/1.92  #Strategies tried      : 1
% 4.58/1.92  
% 4.58/1.92  Timing (in seconds)
% 4.58/1.92  ----------------------
% 4.58/1.92  Preprocessing        : 0.29
% 4.58/1.92  Parsing              : 0.16
% 4.58/1.92  CNF conversion       : 0.02
% 4.58/1.92  Main loop            : 0.86
% 4.58/1.92  Inferencing          : 0.26
% 4.58/1.92  Reduction            : 0.38
% 4.58/1.92  Demodulation         : 0.31
% 4.58/1.92  BG Simplification    : 0.03
% 4.58/1.92  Subsumption          : 0.12
% 4.58/1.92  Abstraction          : 0.04
% 4.58/1.92  MUC search           : 0.00
% 4.58/1.92  Cooper               : 0.00
% 4.58/1.92  Total                : 1.18
% 4.58/1.92  Index Insertion      : 0.00
% 4.58/1.93  Index Deletion       : 0.00
% 4.58/1.93  Index Matching       : 0.00
% 4.58/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
