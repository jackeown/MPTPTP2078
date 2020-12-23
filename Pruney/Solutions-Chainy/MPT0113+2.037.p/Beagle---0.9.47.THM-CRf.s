%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:16 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 108 expanded)
%              Number of equality atoms :   33 (  48 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_1737,plain,(
    ! [A_81,B_82] :
      ( r1_xboole_0(A_81,B_82)
      | k3_xboole_0(A_81,B_82) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | k4_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_137,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_129,c_30])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_228,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_252,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_407,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_422,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_407])).

tff(c_437,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_422])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1008,plain,(
    ! [A_65,B_66] : k3_xboole_0(k4_xboole_0(A_65,B_66),A_65) = k4_xboole_0(A_65,B_66) ),
    inference(resolution,[status(thm)],[c_18,c_228])).

tff(c_454,plain,(
    ! [A_52,B_53,C_54] : k3_xboole_0(k3_xboole_0(A_52,B_53),C_54) = k3_xboole_0(A_52,k3_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_496,plain,(
    ! [C_54] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_54)) = k3_xboole_0('#skF_1',C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_454])).

tff(c_1026,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_496])).

tff(c_1083,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_1026])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1589,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1083,c_12])).

tff(c_1592,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_1589])).

tff(c_1594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1592])).

tff(c_1595,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1745,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1737,c_1595])).

tff(c_20,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1630,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1638,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1630])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1637,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1630])).

tff(c_1902,plain,(
    ! [A_92,B_93] :
      ( k3_xboole_0(A_92,B_93) = A_92
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1933,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1902])).

tff(c_2070,plain,(
    ! [A_100,B_101,C_102] : k3_xboole_0(k3_xboole_0(A_100,B_101),C_102) = k3_xboole_0(A_100,k3_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2306,plain,(
    ! [C_108] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_108)) = k3_xboole_0('#skF_1',C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1933,c_2070])).

tff(c_2329,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_2306])).

tff(c_2347,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_2329])).

tff(c_2349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1745,c_2347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.85  
% 4.14/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.85  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.14/1.85  
% 4.14/1.85  %Foreground sorts:
% 4.14/1.85  
% 4.14/1.85  
% 4.14/1.85  %Background operators:
% 4.14/1.85  
% 4.14/1.85  
% 4.14/1.85  %Foreground operators:
% 4.14/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.14/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.14/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.14/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.14/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.14/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.14/1.85  
% 4.14/1.86  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.14/1.86  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.14/1.86  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.14/1.86  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/1.86  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.14/1.86  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.14/1.86  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.14/1.86  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.14/1.86  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.14/1.86  tff(c_1737, plain, (![A_81, B_82]: (r1_xboole_0(A_81, B_82) | k3_xboole_0(A_81, B_82)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.86  tff(c_129, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | k4_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/1.86  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.14/1.86  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 4.14/1.86  tff(c_137, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_129, c_30])).
% 4.14/1.86  tff(c_26, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.14/1.86  tff(c_64, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/1.86  tff(c_72, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_64])).
% 4.14/1.86  tff(c_228, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.14/1.86  tff(c_252, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_228])).
% 4.14/1.86  tff(c_407, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.14/1.86  tff(c_422, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_252, c_407])).
% 4.14/1.86  tff(c_437, plain, (k5_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_422])).
% 4.14/1.86  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.14/1.86  tff(c_1008, plain, (![A_65, B_66]: (k3_xboole_0(k4_xboole_0(A_65, B_66), A_65)=k4_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_18, c_228])).
% 4.14/1.86  tff(c_454, plain, (![A_52, B_53, C_54]: (k3_xboole_0(k3_xboole_0(A_52, B_53), C_54)=k3_xboole_0(A_52, k3_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.14/1.86  tff(c_496, plain, (![C_54]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_54))=k3_xboole_0('#skF_1', C_54))), inference(superposition, [status(thm), theory('equality')], [c_252, c_454])).
% 4.14/1.86  tff(c_1026, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_496])).
% 4.14/1.86  tff(c_1083, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_1026])).
% 4.14/1.86  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.14/1.86  tff(c_1589, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1083, c_12])).
% 4.14/1.86  tff(c_1592, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_437, c_1589])).
% 4.14/1.86  tff(c_1594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_1592])).
% 4.14/1.86  tff(c_1595, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 4.14/1.86  tff(c_1745, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1737, c_1595])).
% 4.14/1.86  tff(c_20, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.14/1.86  tff(c_1630, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.86  tff(c_1638, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1630])).
% 4.14/1.86  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.86  tff(c_1637, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1630])).
% 4.14/1.86  tff(c_1902, plain, (![A_92, B_93]: (k3_xboole_0(A_92, B_93)=A_92 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.14/1.86  tff(c_1933, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1902])).
% 4.14/1.86  tff(c_2070, plain, (![A_100, B_101, C_102]: (k3_xboole_0(k3_xboole_0(A_100, B_101), C_102)=k3_xboole_0(A_100, k3_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.14/1.86  tff(c_2306, plain, (![C_108]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_108))=k3_xboole_0('#skF_1', C_108))), inference(superposition, [status(thm), theory('equality')], [c_1933, c_2070])).
% 4.14/1.86  tff(c_2329, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1637, c_2306])).
% 4.14/1.86  tff(c_2347, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_2329])).
% 4.14/1.86  tff(c_2349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1745, c_2347])).
% 4.14/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.86  
% 4.14/1.86  Inference rules
% 4.14/1.86  ----------------------
% 4.14/1.86  #Ref     : 0
% 4.14/1.86  #Sup     : 609
% 4.14/1.86  #Fact    : 0
% 4.14/1.86  #Define  : 0
% 4.14/1.86  #Split   : 3
% 4.14/1.86  #Chain   : 0
% 4.14/1.86  #Close   : 0
% 4.14/1.86  
% 4.14/1.86  Ordering : KBO
% 4.14/1.86  
% 4.14/1.86  Simplification rules
% 4.14/1.86  ----------------------
% 4.14/1.86  #Subsume      : 11
% 4.14/1.86  #Demod        : 420
% 4.14/1.86  #Tautology    : 397
% 4.14/1.86  #SimpNegUnit  : 2
% 4.14/1.86  #BackRed      : 2
% 4.14/1.86  
% 4.14/1.86  #Partial instantiations: 0
% 4.14/1.86  #Strategies tried      : 1
% 4.14/1.86  
% 4.14/1.87  Timing (in seconds)
% 4.14/1.87  ----------------------
% 4.14/1.87  Preprocessing        : 0.33
% 4.14/1.87  Parsing              : 0.19
% 4.14/1.87  CNF conversion       : 0.02
% 4.14/1.87  Main loop            : 0.72
% 4.14/1.87  Inferencing          : 0.25
% 4.14/1.87  Reduction            : 0.30
% 4.14/1.87  Demodulation         : 0.25
% 4.14/1.87  BG Simplification    : 0.03
% 4.14/1.87  Subsumption          : 0.10
% 4.14/1.87  Abstraction          : 0.03
% 4.14/1.87  MUC search           : 0.00
% 4.14/1.87  Cooper               : 0.00
% 4.14/1.87  Total                : 1.09
% 4.14/1.87  Index Insertion      : 0.00
% 4.14/1.87  Index Deletion       : 0.00
% 4.14/1.87  Index Matching       : 0.00
% 4.14/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
