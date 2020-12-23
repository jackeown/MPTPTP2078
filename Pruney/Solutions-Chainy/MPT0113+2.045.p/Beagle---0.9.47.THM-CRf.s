%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 103 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_26,B_27] : r1_tarski(k3_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_359,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | k4_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_371,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_359,c_95])).

tff(c_97,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_18])).

tff(c_152,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [A_42] : k3_xboole_0(k1_xboole_0,A_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_152])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_186,plain,(
    ! [A_42] : k3_xboole_0(A_42,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_117,plain,(
    ! [A_15,B_16] : k4_xboole_0(k4_xboole_0(A_15,B_16),A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_152])).

tff(c_525,plain,(
    ! [A_62,B_63,C_64] : k4_xboole_0(k3_xboole_0(A_62,B_63),C_64) = k3_xboole_0(A_62,k4_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_654,plain,(
    ! [C_67] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_67)) = k4_xboole_0('#skF_1',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_525])).

tff(c_690,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_654])).

tff(c_701,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_690])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_701])).

tff(c_705,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_739,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_758,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_705,c_739])).

tff(c_1171,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(k3_xboole_0(A_94,B_95),C_96) = k3_xboole_0(A_94,k4_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1583,plain,(
    ! [C_110] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_110)) = k4_xboole_0('#skF_1',C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_1171])).

tff(c_763,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_739])).

tff(c_1605,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_763])).

tff(c_1043,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(A_84,k4_xboole_0(C_85,B_86))
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1058,plain,(
    ! [C_85,B_86,A_84] :
      ( r1_xboole_0(k4_xboole_0(C_85,B_86),A_84)
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(resolution,[status(thm)],[c_1043,c_6])).

tff(c_1839,plain,(
    ! [A_113] :
      ( r1_xboole_0('#skF_1',A_113)
      | ~ r1_tarski(A_113,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1605,c_1058])).

tff(c_704,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1844,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1839,c_704])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.56  
% 3.24/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.57  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.57  
% 3.24/1.57  %Foreground sorts:
% 3.24/1.57  
% 3.24/1.57  
% 3.24/1.57  %Background operators:
% 3.24/1.57  
% 3.24/1.57  
% 3.24/1.57  %Foreground operators:
% 3.24/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.57  
% 3.24/1.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.24/1.58  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.24/1.58  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.24/1.58  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.24/1.58  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.24/1.58  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.24/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.58  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.24/1.58  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.24/1.58  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.24/1.58  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.24/1.58  tff(c_37, plain, (![A_26, B_27]: (r1_tarski(k3_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.24/1.58  tff(c_40, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 3.24/1.58  tff(c_359, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | k4_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.58  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.24/1.58  tff(c_95, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 3.24/1.58  tff(c_371, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_359, c_95])).
% 3.24/1.58  tff(c_97, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.58  tff(c_118, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_97])).
% 3.24/1.58  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.58  tff(c_123, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(superposition, [status(thm), theory('equality')], [c_118, c_18])).
% 3.24/1.58  tff(c_152, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.58  tff(c_178, plain, (![A_42]: (k3_xboole_0(k1_xboole_0, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_152])).
% 3.24/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.58  tff(c_186, plain, (![A_42]: (k3_xboole_0(A_42, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 3.24/1.58  tff(c_117, plain, (![A_15, B_16]: (k4_xboole_0(k4_xboole_0(A_15, B_16), A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_97])).
% 3.24/1.58  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.24/1.58  tff(c_176, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_152])).
% 3.24/1.58  tff(c_525, plain, (![A_62, B_63, C_64]: (k4_xboole_0(k3_xboole_0(A_62, B_63), C_64)=k3_xboole_0(A_62, k4_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_654, plain, (![C_67]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_67))=k4_xboole_0('#skF_1', C_67))), inference(superposition, [status(thm), theory('equality')], [c_176, c_525])).
% 3.24/1.58  tff(c_690, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_654])).
% 3.24/1.58  tff(c_701, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_186, c_690])).
% 3.24/1.58  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_701])).
% 3.24/1.58  tff(c_705, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 3.24/1.58  tff(c_739, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.58  tff(c_758, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_705, c_739])).
% 3.24/1.58  tff(c_1171, plain, (![A_94, B_95, C_96]: (k4_xboole_0(k3_xboole_0(A_94, B_95), C_96)=k3_xboole_0(A_94, k4_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.58  tff(c_1583, plain, (![C_110]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_110))=k4_xboole_0('#skF_1', C_110))), inference(superposition, [status(thm), theory('equality')], [c_758, c_1171])).
% 3.24/1.58  tff(c_763, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_739])).
% 3.24/1.58  tff(c_1605, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1583, c_763])).
% 3.24/1.58  tff(c_1043, plain, (![A_84, C_85, B_86]: (r1_xboole_0(A_84, k4_xboole_0(C_85, B_86)) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.58  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.58  tff(c_1058, plain, (![C_85, B_86, A_84]: (r1_xboole_0(k4_xboole_0(C_85, B_86), A_84) | ~r1_tarski(A_84, B_86))), inference(resolution, [status(thm)], [c_1043, c_6])).
% 3.24/1.58  tff(c_1839, plain, (![A_113]: (r1_xboole_0('#skF_1', A_113) | ~r1_tarski(A_113, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1605, c_1058])).
% 3.24/1.58  tff(c_704, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 3.24/1.58  tff(c_1844, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1839, c_704])).
% 3.24/1.58  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1844])).
% 3.24/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.58  
% 3.24/1.58  Inference rules
% 3.24/1.58  ----------------------
% 3.24/1.58  #Ref     : 0
% 3.24/1.58  #Sup     : 475
% 3.24/1.58  #Fact    : 0
% 3.24/1.58  #Define  : 0
% 3.24/1.58  #Split   : 1
% 3.24/1.58  #Chain   : 0
% 3.24/1.58  #Close   : 0
% 3.24/1.58  
% 3.24/1.58  Ordering : KBO
% 3.24/1.58  
% 3.24/1.58  Simplification rules
% 3.24/1.58  ----------------------
% 3.24/1.58  #Subsume      : 2
% 3.24/1.58  #Demod        : 270
% 3.24/1.58  #Tautology    : 353
% 3.24/1.58  #SimpNegUnit  : 1
% 3.24/1.58  #BackRed      : 0
% 3.24/1.58  
% 3.24/1.58  #Partial instantiations: 0
% 3.24/1.58  #Strategies tried      : 1
% 3.24/1.58  
% 3.24/1.58  Timing (in seconds)
% 3.24/1.58  ----------------------
% 3.24/1.58  Preprocessing        : 0.30
% 3.24/1.58  Parsing              : 0.16
% 3.24/1.58  CNF conversion       : 0.02
% 3.24/1.58  Main loop            : 0.50
% 3.24/1.58  Inferencing          : 0.18
% 3.24/1.58  Reduction            : 0.19
% 3.24/1.59  Demodulation         : 0.15
% 3.24/1.59  BG Simplification    : 0.02
% 3.24/1.59  Subsumption          : 0.07
% 3.24/1.59  Abstraction          : 0.03
% 3.24/1.59  MUC search           : 0.00
% 3.24/1.59  Cooper               : 0.00
% 3.24/1.59  Total                : 0.83
% 3.24/1.59  Index Insertion      : 0.00
% 3.24/1.59  Index Deletion       : 0.00
% 3.24/1.59  Index Matching       : 0.00
% 3.24/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
