%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 681 expanded)
%              Number of leaves         :   21 ( 241 expanded)
%              Depth                    :   13
%              Number of atoms          :   44 ( 774 expanded)
%              Number of equality atoms :   43 ( 773 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_42,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_53,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_24] : k2_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | k2_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4])).

tff(c_178,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_20])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_178])).

tff(c_16,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_16])).

tff(c_184,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_174])).

tff(c_290,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_299,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_290])).

tff(c_305,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_299])).

tff(c_350,plain,(
    ! [A_40,B_41] :
      ( A_40 = '#skF_3'
      | k2_xboole_0(A_40,B_41) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_179,c_4])).

tff(c_366,plain,(
    '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_350])).

tff(c_34,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [A_17] : k1_tarski(A_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_34])).

tff(c_187,plain,(
    ! [A_17] : k1_tarski(A_17) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_38])).

tff(c_376,plain,(
    ! [A_17] : k1_tarski(A_17) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_187])).

tff(c_185,plain,(
    ! [A_24] : k2_xboole_0('#skF_3',A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_83])).

tff(c_373,plain,(
    ! [A_24] : k2_xboole_0('#skF_1',A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_185])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_423,plain,(
    ! [A_44] : k2_xboole_0('#skF_1',A_44) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_185])).

tff(c_371,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_305])).

tff(c_433,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_371])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_179])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_169,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_386,plain,(
    k2_xboole_0('#skF_1',k2_tarski('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_366,c_169])).

tff(c_496,plain,(
    k2_xboole_0('#skF_1',k2_tarski('#skF_1','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_386])).

tff(c_498,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_8,c_496])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.24  
% 1.98/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.98/1.25  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.98/1.25  tff(f_49, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.98/1.25  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.98/1.25  tff(f_42, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.98/1.25  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.98/1.25  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.98/1.25  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.98/1.25  tff(c_53, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.25  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.25  tff(c_83, plain, (![A_24]: (k2_xboole_0(k1_xboole_0, A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_53, c_6])).
% 1.98/1.25  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.25  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | k2_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.25  tff(c_174, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_4])).
% 1.98/1.25  tff(c_178, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_20])).
% 1.98/1.25  tff(c_179, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_178])).
% 1.98/1.25  tff(c_16, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.25  tff(c_190, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_16])).
% 1.98/1.25  tff(c_184, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_174])).
% 1.98/1.25  tff(c_290, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.25  tff(c_299, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_290])).
% 1.98/1.25  tff(c_305, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_299])).
% 1.98/1.25  tff(c_350, plain, (![A_40, B_41]: (A_40='#skF_3' | k2_xboole_0(A_40, B_41)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_179, c_4])).
% 1.98/1.25  tff(c_366, plain, ('#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_305, c_350])).
% 1.98/1.25  tff(c_34, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.25  tff(c_38, plain, (![A_17]: (k1_tarski(A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_34])).
% 1.98/1.25  tff(c_187, plain, (![A_17]: (k1_tarski(A_17)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_38])).
% 1.98/1.25  tff(c_376, plain, (![A_17]: (k1_tarski(A_17)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_187])).
% 1.98/1.25  tff(c_185, plain, (![A_24]: (k2_xboole_0('#skF_3', A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_83])).
% 1.98/1.25  tff(c_373, plain, (![A_24]: (k2_xboole_0('#skF_1', A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_185])).
% 1.98/1.25  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.25  tff(c_423, plain, (![A_44]: (k2_xboole_0('#skF_1', A_44)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_185])).
% 1.98/1.25  tff(c_371, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_305])).
% 1.98/1.25  tff(c_433, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_423, c_371])).
% 1.98/1.25  tff(c_377, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_179])).
% 1.98/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.25  tff(c_169, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_20])).
% 1.98/1.25  tff(c_386, plain, (k2_xboole_0('#skF_1', k2_tarski('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_366, c_169])).
% 1.98/1.25  tff(c_496, plain, (k2_xboole_0('#skF_1', k2_tarski('#skF_1', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_386])).
% 1.98/1.25  tff(c_498, plain, (k1_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_8, c_496])).
% 1.98/1.25  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_498])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 0
% 1.98/1.25  #Sup     : 121
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 0
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 7
% 1.98/1.25  #Demod        : 62
% 1.98/1.25  #Tautology    : 90
% 1.98/1.25  #SimpNegUnit  : 1
% 1.98/1.25  #BackRed      : 21
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 1.98/1.26  Preprocessing        : 0.26
% 1.98/1.26  Parsing              : 0.14
% 1.98/1.26  CNF conversion       : 0.01
% 1.98/1.26  Main loop            : 0.20
% 1.98/1.26  Inferencing          : 0.07
% 1.98/1.26  Reduction            : 0.08
% 1.98/1.26  Demodulation         : 0.06
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.03
% 1.98/1.26  Abstraction          : 0.01
% 1.98/1.26  MUC search           : 0.00
% 1.98/1.26  Cooper               : 0.00
% 1.98/1.26  Total                : 0.49
% 1.98/1.26  Index Insertion      : 0.00
% 1.98/1.26  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
