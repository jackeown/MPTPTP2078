%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 185 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :   56 ( 243 expanded)
%              Number of equality atoms :   49 ( 176 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_162,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_177,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_162])).

tff(c_184,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_108,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_108])).

tff(c_227,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_184,c_117])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_180,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_162])).

tff(c_185,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_180])).

tff(c_399,plain,(
    ! [A_35,B_36,C_37] : k4_xboole_0(k4_xboole_0(A_35,B_36),C_37) = k4_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_520,plain,(
    ! [C_39] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_39)) = k4_xboole_0('#skF_3',C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_399])).

tff(c_554,plain,(
    ! [B_2] : k4_xboole_0('#skF_3',k2_xboole_0(B_2,'#skF_2')) = k4_xboole_0('#skF_3',B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_520])).

tff(c_240,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_261,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_240])).

tff(c_276,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_261])).

tff(c_26,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_969,plain,(
    ! [B_50] : k4_xboole_0('#skF_3',k2_xboole_0(B_50,'#skF_2')) = k4_xboole_0('#skF_3',B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_520])).

tff(c_1022,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_969])).

tff(c_1036,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_276,c_1022])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1078,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_8])).

tff(c_1083,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_1078])).

tff(c_120,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_108])).

tff(c_198,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_120])).

tff(c_214,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_2])).

tff(c_264,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_240])).

tff(c_277,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_264])).

tff(c_674,plain,(
    ! [C_42] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_42)) = k4_xboole_0('#skF_1',C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_399])).

tff(c_712,plain,(
    ! [A_1] : k4_xboole_0('#skF_1',k2_xboole_0(A_1,'#skF_2')) = k4_xboole_0('#skF_1',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_674])).

tff(c_2246,plain,(
    ! [A_73] : k4_xboole_0('#skF_1',k2_xboole_0(A_73,'#skF_2')) = k4_xboole_0('#skF_1',A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_674])).

tff(c_2305,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2246])).

tff(c_2321,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_712,c_2305])).

tff(c_2340,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2321,c_8])).

tff(c_2347,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_214,c_2,c_2340])).

tff(c_2349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_2347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:31:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.59  
% 3.57/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.59  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.59  
% 3.57/1.59  %Foreground sorts:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Background operators:
% 3.57/1.59  
% 3.57/1.59  
% 3.57/1.59  %Foreground operators:
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.59  
% 3.57/1.61  tff(f_52, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.57/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.57/1.61  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.57/1.61  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.57/1.61  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.57/1.61  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.57/1.61  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.57/1.61  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.57/1.61  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.57/1.61  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.61  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.57/1.61  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.61  tff(c_74, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.61  tff(c_86, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_74])).
% 3.57/1.61  tff(c_162, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.57/1.61  tff(c_177, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_162])).
% 3.57/1.61  tff(c_184, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_177])).
% 3.57/1.61  tff(c_108, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.57/1.61  tff(c_117, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_86, c_108])).
% 3.57/1.61  tff(c_227, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_184, c_117])).
% 3.57/1.61  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.61  tff(c_85, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_74])).
% 3.57/1.61  tff(c_180, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_162])).
% 3.57/1.61  tff(c_185, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_180])).
% 3.57/1.61  tff(c_399, plain, (![A_35, B_36, C_37]: (k4_xboole_0(k4_xboole_0(A_35, B_36), C_37)=k4_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.61  tff(c_520, plain, (![C_39]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_39))=k4_xboole_0('#skF_3', C_39))), inference(superposition, [status(thm), theory('equality')], [c_185, c_399])).
% 3.57/1.61  tff(c_554, plain, (![B_2]: (k4_xboole_0('#skF_3', k2_xboole_0(B_2, '#skF_2'))=k4_xboole_0('#skF_3', B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_520])).
% 3.57/1.61  tff(c_240, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.61  tff(c_261, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_240])).
% 3.57/1.61  tff(c_276, plain, (k4_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_85, c_261])).
% 3.57/1.61  tff(c_26, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.61  tff(c_969, plain, (![B_50]: (k4_xboole_0('#skF_3', k2_xboole_0(B_50, '#skF_2'))=k4_xboole_0('#skF_3', B_50))), inference(superposition, [status(thm), theory('equality')], [c_2, c_520])).
% 3.57/1.61  tff(c_1022, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_969])).
% 3.57/1.61  tff(c_1036, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_554, c_276, c_1022])).
% 3.57/1.61  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.57/1.61  tff(c_1078, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1036, c_8])).
% 3.57/1.61  tff(c_1083, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_1078])).
% 3.57/1.61  tff(c_120, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_85, c_108])).
% 3.57/1.61  tff(c_198, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_120])).
% 3.57/1.61  tff(c_214, plain, (k2_xboole_0('#skF_3', k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_198, c_2])).
% 3.57/1.61  tff(c_264, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_184, c_240])).
% 3.57/1.61  tff(c_277, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_264])).
% 3.57/1.61  tff(c_674, plain, (![C_42]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_42))=k4_xboole_0('#skF_1', C_42))), inference(superposition, [status(thm), theory('equality')], [c_184, c_399])).
% 3.57/1.61  tff(c_712, plain, (![A_1]: (k4_xboole_0('#skF_1', k2_xboole_0(A_1, '#skF_2'))=k4_xboole_0('#skF_1', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_674])).
% 3.57/1.61  tff(c_2246, plain, (![A_73]: (k4_xboole_0('#skF_1', k2_xboole_0(A_73, '#skF_2'))=k4_xboole_0('#skF_1', A_73))), inference(superposition, [status(thm), theory('equality')], [c_2, c_674])).
% 3.57/1.61  tff(c_2305, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2246])).
% 3.57/1.61  tff(c_2321, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_277, c_712, c_2305])).
% 3.57/1.61  tff(c_2340, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2321, c_8])).
% 3.57/1.61  tff(c_2347, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_214, c_2, c_2340])).
% 3.57/1.61  tff(c_2349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_2347])).
% 3.57/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.61  
% 3.57/1.61  Inference rules
% 3.57/1.61  ----------------------
% 3.57/1.61  #Ref     : 0
% 3.57/1.61  #Sup     : 573
% 3.57/1.61  #Fact    : 0
% 3.57/1.61  #Define  : 0
% 3.57/1.61  #Split   : 0
% 3.57/1.61  #Chain   : 0
% 3.57/1.61  #Close   : 0
% 3.57/1.61  
% 3.57/1.61  Ordering : KBO
% 3.57/1.61  
% 3.57/1.61  Simplification rules
% 3.57/1.61  ----------------------
% 3.57/1.61  #Subsume      : 0
% 3.57/1.61  #Demod        : 503
% 3.57/1.61  #Tautology    : 437
% 3.57/1.61  #SimpNegUnit  : 1
% 3.57/1.61  #BackRed      : 3
% 3.57/1.61  
% 3.57/1.61  #Partial instantiations: 0
% 3.57/1.61  #Strategies tried      : 1
% 3.57/1.61  
% 3.57/1.61  Timing (in seconds)
% 3.57/1.61  ----------------------
% 3.57/1.61  Preprocessing        : 0.29
% 3.57/1.61  Parsing              : 0.16
% 3.57/1.61  CNF conversion       : 0.02
% 3.57/1.61  Main loop            : 0.54
% 3.57/1.61  Inferencing          : 0.18
% 3.57/1.61  Reduction            : 0.24
% 3.57/1.61  Demodulation         : 0.19
% 3.57/1.61  BG Simplification    : 0.02
% 3.57/1.61  Subsumption          : 0.07
% 3.57/1.61  Abstraction          : 0.03
% 3.57/1.61  MUC search           : 0.00
% 3.57/1.61  Cooper               : 0.00
% 3.57/1.61  Total                : 0.86
% 3.57/1.61  Index Insertion      : 0.00
% 3.57/1.61  Index Deletion       : 0.00
% 3.57/1.61  Index Matching       : 0.00
% 3.57/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
