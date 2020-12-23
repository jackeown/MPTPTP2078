%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   57 (  98 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 108 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_28,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [B_27,A_28] :
      ( ~ r2_xboole_0(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_196,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k4_xboole_0(B_39,A_38)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_196])).

tff(c_216,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_174,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_182,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_174])).

tff(c_220,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_182])).

tff(c_250,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_263,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_250])).

tff(c_87,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_32] : k5_xboole_0(k1_xboole_0,A_32) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_16])).

tff(c_82,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ r2_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_181,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_86,c_174])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_339,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(B_47,A_46)) = k4_xboole_0(A_46,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_250])).

tff(c_369,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_339])).

tff(c_386,plain,(
    k5_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_369])).

tff(c_405,plain,(
    ! [A_48,B_49,C_50] : k5_xboole_0(k5_xboole_0(A_48,B_49),C_50) = k5_xboole_0(A_48,k5_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_442,plain,(
    ! [C_50] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_50)) = k5_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_405])).

tff(c_540,plain,(
    ! [C_52] : k5_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_52)) = C_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_442])).

tff(c_559,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_540])).

tff(c_269,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_250])).

tff(c_307,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_269])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_311,plain,(
    k5_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_1')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_24])).

tff(c_750,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_311])).

tff(c_757,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_20])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.53/1.35  
% 2.53/1.35  %Foreground sorts:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Background operators:
% 2.53/1.35  
% 2.53/1.35  
% 2.53/1.35  %Foreground operators:
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.53/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.35  
% 2.53/1.36  tff(f_61, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.53/1.36  tff(f_49, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.53/1.36  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.53/1.36  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.53/1.36  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.53/1.36  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.53/1.36  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.53/1.36  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.53/1.36  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.53/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.53/1.36  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.53/1.36  tff(c_28, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.36  tff(c_77, plain, (![B_27, A_28]: (~r2_xboole_0(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.36  tff(c_81, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.53/1.36  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.53/1.36  tff(c_26, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.36  tff(c_196, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k4_xboole_0(B_39, A_38))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.36  tff(c_213, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_196])).
% 2.53/1.36  tff(c_216, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_213])).
% 2.53/1.36  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.36  tff(c_174, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.36  tff(c_182, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(resolution, [status(thm)], [c_20, c_174])).
% 2.53/1.36  tff(c_220, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_216, c_182])).
% 2.53/1.36  tff(c_250, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.36  tff(c_263, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_220, c_250])).
% 2.53/1.36  tff(c_87, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.36  tff(c_103, plain, (![A_32]: (k5_xboole_0(k1_xboole_0, A_32)=A_32)), inference(superposition, [status(thm), theory('equality')], [c_87, c_16])).
% 2.53/1.36  tff(c_82, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~r2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.36  tff(c_86, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_82])).
% 2.53/1.36  tff(c_181, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_86, c_174])).
% 2.53/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.36  tff(c_339, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(B_47, A_46))=k4_xboole_0(A_46, B_47))), inference(superposition, [status(thm), theory('equality')], [c_2, c_250])).
% 2.53/1.36  tff(c_369, plain, (k5_xboole_0('#skF_2', '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_181, c_339])).
% 2.53/1.36  tff(c_386, plain, (k5_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_369])).
% 2.53/1.36  tff(c_405, plain, (![A_48, B_49, C_50]: (k5_xboole_0(k5_xboole_0(A_48, B_49), C_50)=k5_xboole_0(A_48, k5_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.36  tff(c_442, plain, (![C_50]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_50))=k5_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_386, c_405])).
% 2.53/1.36  tff(c_540, plain, (![C_52]: (k5_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_52))=C_52)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_442])).
% 2.53/1.36  tff(c_559, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_263, c_540])).
% 2.53/1.36  tff(c_269, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_181, c_250])).
% 2.53/1.36  tff(c_307, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_269])).
% 2.53/1.36  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.36  tff(c_311, plain, (k5_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_307, c_24])).
% 2.53/1.36  tff(c_750, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_559, c_311])).
% 2.53/1.36  tff(c_757, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_750, c_20])).
% 2.53/1.36  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_757])).
% 2.53/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.36  
% 2.53/1.36  Inference rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Ref     : 0
% 2.53/1.36  #Sup     : 187
% 2.53/1.36  #Fact    : 0
% 2.53/1.36  #Define  : 0
% 2.53/1.36  #Split   : 0
% 2.53/1.36  #Chain   : 0
% 2.53/1.36  #Close   : 0
% 2.53/1.36  
% 2.53/1.36  Ordering : KBO
% 2.53/1.36  
% 2.53/1.36  Simplification rules
% 2.53/1.36  ----------------------
% 2.53/1.36  #Subsume      : 4
% 2.53/1.36  #Demod        : 63
% 2.53/1.36  #Tautology    : 124
% 2.53/1.36  #SimpNegUnit  : 1
% 2.53/1.36  #BackRed      : 0
% 2.53/1.36  
% 2.53/1.36  #Partial instantiations: 0
% 2.53/1.36  #Strategies tried      : 1
% 2.53/1.36  
% 2.53/1.36  Timing (in seconds)
% 2.53/1.36  ----------------------
% 2.71/1.37  Preprocessing        : 0.28
% 2.71/1.37  Parsing              : 0.16
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.33
% 2.71/1.37  Inferencing          : 0.13
% 2.71/1.37  Reduction            : 0.12
% 2.71/1.37  Demodulation         : 0.10
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.05
% 2.71/1.37  Abstraction          : 0.01
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.64
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
