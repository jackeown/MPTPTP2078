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
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  86 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_3564,plain,(
    ! [A_133,B_134] :
      ( r1_xboole_0(A_133,B_134)
      | k3_xboole_0(A_133,B_134) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_204,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_212,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_62])).

tff(c_26,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_155,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_429,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k4_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3187,plain,(
    ! [A_127,C_128] : k3_xboole_0(A_127,k4_xboole_0(A_127,C_128)) = k4_xboole_0(A_127,C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_429])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_12,B_13] : k4_xboole_0(k3_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_3435,plain,(
    ! [A_131,C_132] : k4_xboole_0(k4_xboole_0(A_131,C_132),A_131) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_74])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_291,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_313,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_291])).

tff(c_456,plain,(
    ! [C_67] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_67)) = k4_xboole_0('#skF_1',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_429])).

tff(c_3477,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3435,c_456])).

tff(c_3559,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_3477])).

tff(c_3561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_3559])).

tff(c_3562,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_3568,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3564,c_3562])).

tff(c_3598,plain,(
    ! [A_139,B_140] :
      ( k3_xboole_0(A_139,B_140) = k1_xboole_0
      | ~ r1_xboole_0(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3610,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_3598])).

tff(c_28,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3609,plain,(
    ! [A_24,B_25] : k3_xboole_0(k4_xboole_0(A_24,B_25),B_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_3598])).

tff(c_3740,plain,(
    ! [A_147,B_148] :
      ( k3_xboole_0(A_147,B_148) = A_147
      | ~ r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3766,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_3740])).

tff(c_4539,plain,(
    ! [A_184,B_185,C_186] : k3_xboole_0(k3_xboole_0(A_184,B_185),C_186) = k3_xboole_0(A_184,k3_xboole_0(B_185,C_186)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4748,plain,(
    ! [C_189] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_189)) = k3_xboole_0('#skF_1',C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_3766,c_4539])).

tff(c_4793,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_4748])).

tff(c_4811,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3610,c_4793])).

tff(c_4813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3568,c_4811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.86  
% 4.33/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.86  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.33/1.86  
% 4.33/1.86  %Foreground sorts:
% 4.33/1.86  
% 4.33/1.86  
% 4.33/1.86  %Background operators:
% 4.33/1.86  
% 4.33/1.86  
% 4.33/1.86  %Foreground operators:
% 4.33/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.33/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.33/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.33/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.33/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.86  
% 4.33/1.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.33/1.87  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.33/1.87  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.33/1.87  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.33/1.87  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.33/1.87  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.33/1.87  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.33/1.87  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.33/1.87  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.33/1.87  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.33/1.87  tff(c_3564, plain, (![A_133, B_134]: (r1_xboole_0(A_133, B_134) | k3_xboole_0(A_133, B_134)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.87  tff(c_204, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | k4_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/1.87  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.33/1.87  tff(c_62, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 4.33/1.87  tff(c_212, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_62])).
% 4.33/1.87  tff(c_26, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.33/1.87  tff(c_155, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.87  tff(c_172, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_155])).
% 4.33/1.87  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.33/1.87  tff(c_429, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k4_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.33/1.87  tff(c_3187, plain, (![A_127, C_128]: (k3_xboole_0(A_127, k4_xboole_0(A_127, C_128))=k4_xboole_0(A_127, C_128))), inference(superposition, [status(thm), theory('equality')], [c_6, c_429])).
% 4.33/1.87  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.33/1.87  tff(c_63, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/1.87  tff(c_74, plain, (![A_12, B_13]: (k4_xboole_0(k3_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_63])).
% 4.33/1.87  tff(c_3435, plain, (![A_131, C_132]: (k4_xboole_0(k4_xboole_0(A_131, C_132), A_131)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3187, c_74])).
% 4.33/1.87  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.33/1.87  tff(c_291, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.33/1.87  tff(c_313, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_291])).
% 4.33/1.87  tff(c_456, plain, (![C_67]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_67))=k4_xboole_0('#skF_1', C_67))), inference(superposition, [status(thm), theory('equality')], [c_313, c_429])).
% 4.33/1.87  tff(c_3477, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3435, c_456])).
% 4.33/1.87  tff(c_3559, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_3477])).
% 4.33/1.87  tff(c_3561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_3559])).
% 4.33/1.87  tff(c_3562, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 4.33/1.87  tff(c_3568, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3564, c_3562])).
% 4.33/1.87  tff(c_3598, plain, (![A_139, B_140]: (k3_xboole_0(A_139, B_140)=k1_xboole_0 | ~r1_xboole_0(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.87  tff(c_3610, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_3598])).
% 4.33/1.87  tff(c_28, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.33/1.87  tff(c_3609, plain, (![A_24, B_25]: (k3_xboole_0(k4_xboole_0(A_24, B_25), B_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_3598])).
% 4.33/1.87  tff(c_3740, plain, (![A_147, B_148]: (k3_xboole_0(A_147, B_148)=A_147 | ~r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.33/1.87  tff(c_3766, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_3740])).
% 4.33/1.87  tff(c_4539, plain, (![A_184, B_185, C_186]: (k3_xboole_0(k3_xboole_0(A_184, B_185), C_186)=k3_xboole_0(A_184, k3_xboole_0(B_185, C_186)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.33/1.87  tff(c_4748, plain, (![C_189]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_189))=k3_xboole_0('#skF_1', C_189))), inference(superposition, [status(thm), theory('equality')], [c_3766, c_4539])).
% 4.33/1.87  tff(c_4793, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3609, c_4748])).
% 4.33/1.87  tff(c_4811, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3610, c_4793])).
% 4.33/1.87  tff(c_4813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3568, c_4811])).
% 4.33/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.87  
% 4.33/1.87  Inference rules
% 4.33/1.87  ----------------------
% 4.33/1.87  #Ref     : 0
% 4.33/1.87  #Sup     : 1225
% 4.33/1.87  #Fact    : 0
% 4.33/1.87  #Define  : 0
% 4.33/1.87  #Split   : 2
% 4.33/1.87  #Chain   : 0
% 4.33/1.87  #Close   : 0
% 4.33/1.87  
% 4.33/1.87  Ordering : KBO
% 4.33/1.87  
% 4.33/1.87  Simplification rules
% 4.33/1.87  ----------------------
% 4.33/1.87  #Subsume      : 91
% 4.33/1.87  #Demod        : 768
% 4.33/1.87  #Tautology    : 787
% 4.33/1.87  #SimpNegUnit  : 21
% 4.33/1.87  #BackRed      : 0
% 4.33/1.87  
% 4.33/1.87  #Partial instantiations: 0
% 4.33/1.87  #Strategies tried      : 1
% 4.33/1.87  
% 4.33/1.87  Timing (in seconds)
% 4.33/1.87  ----------------------
% 4.33/1.87  Preprocessing        : 0.32
% 4.33/1.87  Parsing              : 0.17
% 4.33/1.88  CNF conversion       : 0.02
% 4.33/1.88  Main loop            : 0.75
% 4.33/1.88  Inferencing          : 0.27
% 4.33/1.88  Reduction            : 0.29
% 4.33/1.88  Demodulation         : 0.22
% 4.33/1.88  BG Simplification    : 0.03
% 4.33/1.88  Subsumption          : 0.11
% 4.33/1.88  Abstraction          : 0.04
% 4.33/1.88  MUC search           : 0.00
% 4.33/1.88  Cooper               : 0.00
% 4.33/1.88  Total                : 1.09
% 4.33/1.88  Index Insertion      : 0.00
% 4.33/1.88  Index Deletion       : 0.00
% 4.33/1.88  Index Matching       : 0.00
% 4.33/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
